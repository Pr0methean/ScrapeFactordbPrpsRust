use std::collections::HashSet;
use std::hint::unreachable_unchecked;
use std::iter::repeat;
use compact_str::CompactString;
use itertools::Itertools;
use log::{info, warn};
use num::Integer;
use num_modular::{ModularCoreOps, ModularPow};
use num_prime::detail::SMALL_PRIMES;
use num_prime::ExactRoots;
use num_prime::nt_funcs::factorize128;
use regex::{Regex, RegexSet};

pub struct FactorFinder {
    regexes: Box<[Regex]>,
    regexes_as_set: RegexSet
}

fn power_multiset<T: PartialEq + Ord + Copy>(multiset: &mut Vec<T>) -> Vec<Vec<T>> {
    let mut result = Vec::new();
    multiset.sort_unstable(); // Sort to handle duplicates more easily

    fn generate_subsets<T: PartialEq + Copy>(
        current_subset: &mut Vec<T>,
        remaining_elements: &mut Vec<T>,
        all_subsets: &mut Vec<Vec<T>>,
    ) {
        // Add the current subset to the result
        all_subsets.push(current_subset.clone());

        if remaining_elements.is_empty() {
            return;
        }

        let mut i = 0;
        while i < remaining_elements.len() {
            let element = remaining_elements.remove(i);
            current_subset.push(element.clone());

            generate_subsets(current_subset, remaining_elements, all_subsets);

            // Backtrack: add the element back and remove from current_subset
            current_subset.pop();
            remaining_elements.insert(i, element);

            // Skip duplicate elements to avoid redundant subsets
            while i < remaining_elements.len() && remaining_elements[i] == element {
                i += 1;
            }
        }
    }

    let mut current_subset = Vec::new();
    generate_subsets(&mut current_subset, multiset, &mut result);

    result
}

impl FactorFinder {
    pub fn new() -> FactorFinder {
        let regexes_as_set = RegexSet::new(&[
            "^lucas\\(([0-9]+)\\)$",
            "^I\\(([0-9]+)\\)$",
            "^([0-9]+)\\^([0-9]+)(\\*[0-9]+)?([+-][0-9]+)?$",
            "^([0-9]+)$",
            "^\\(([^()]+)\\)$",
            "^([^+-]+|\\([^()]+\\))/([0-9]+)$",
            "^([^+-]+|\\([^()]+\\))/([^+-]+|\\([^()]+\\))$",
            "^([^+-]+|\\([^()]+\\))\\*([^+-]+|\\([^()]+\\))$",
        ]).unwrap();
        let regexes = regexes_as_set.patterns()
            .iter()
            .map(|pat| Regex::new(pat).unwrap())
            .collect();
        FactorFinder {
            regexes, regexes_as_set
        }
    }

    pub fn find_factors(&self, expr: &str) -> Box<[CompactString]> {
        info!("Searching for factors of expression {expr}");
        let mut factors = Vec::new();
        if let Some(index) = self.regexes_as_set.matches(expr).into_iter().next() {
            let captures = self.regexes[index].captures(expr).unwrap();
            match index {
                0 => { // Lucas number
                    let Ok(term_number) = captures[1].parse::<u128>() else {
                        warn!("Could not parse term number of a Lucas number: {}", &captures[1]);
                        return Box::new([]);
                    };
                    let mut factors_of_term = factorize128(term_number);
                    let power_of_2 = factors_of_term.remove(&2).unwrap_or(0) as u128;
                    let mut factors_of_term = factors_of_term.into_iter()
                        .flat_map(|(key, value)| repeat(key).take(value))
                        .collect::<Vec<u128>>();
                    let full_set_size = factors_of_term.len();
                    for subset in power_multiset(&mut factors_of_term).into_iter() {
                        if subset.len() < full_set_size {
                            let product = subset.into_iter().product::<u128>() << power_of_2;
                            if product > 2 {
                                factors.push(format!("lucas({product})").into());
                            }
                        }
                    }
                }
                1 => { // Fibonacci number
                    let Ok(term_number) = captures[1].parse::<u128>() else {
                        warn!("Could not parse term number of a Fibonacci number: {}", &captures[1]);
                        return Box::new([]);
                    };
                    if term_number % 2 == 0 {
                        factors.push(format!("lucas({})", term_number >> 1).into());
                    }
                    let factors_of_term = factorize128(term_number);
                    let mut factors_of_term = factors_of_term.into_iter()
                        .flat_map(|(key, value)| repeat(key).take(value))
                        .collect::<Vec<u128>>();
                    let full_set_size = factors_of_term.len();
                    for subset in power_multiset(&mut factors_of_term).into_iter() {
                        if subset.len() < full_set_size && subset.len() > 0 {
                            let product: u128 = subset.into_iter().product();
                            if product > 2 {
                                factors.push(format!("I({product})").into());
                            }
                        }
                    }
                }
                2 => { // a^n*b + c
                    let Ok(a) = captures[1].parse::<u128>() else {
                        warn!("Could not parse a in an a^n*b + c expression: {}", &captures[1]);
                        return Box::new([]);
                    };
                    let Ok(n) = captures[2].parse::<u128>() else {
                        warn!("Could not parse n in an a^n*b + c expression: {}", &captures[2]);
                        return Box::new([]);
                    };
                    let mut b = 1u128;
                    if let Some(b_match) = captures.get(3) && let Ok(parsed_b) = b_match.as_str().parse::<u128>() {
                        b = parsed_b;
                    }
                    let mut c = 0i128;
                    if let Some(c_match) = captures.get(4) && let Ok(parsed_c) = c_match.as_str().parse::<i128>() {
                        c = parsed_c;
                    };
                    let gcd_ac = a.gcd(&c.unsigned_abs());
                    let gcd_bc = b.gcd(&c.unsigned_abs());
                    if gcd_ac > 1 {
                        factors.push(gcd_ac.to_string().into());
                    }
                    if gcd_bc > 1 {
                        factors.push(gcd_bc.to_string().into());
                    }
                    b /= gcd_bc;
                    c /= gcd_bc as i128;
                    for prime in SMALL_PRIMES {
                        let prime = prime as u128;
                        if (a.powm(n, &prime).mulm(b, &prime) as i128 + c) % (prime as i128) == 0 {
                            factors.push(prime.to_string().into());
                        }
                        if n % prime == 0 {
                            if let Ok(prime_for_root) = prime.try_into()
                                && (prime != 2 || c > 0)
                                && let Some(root_c) = c.nth_root_exact(prime_for_root)
                                && let Some(root_b) = b.nth_root_exact(prime_for_root) {
                                factors.push(format!("{}{}{}{}", a,
                                                     if (n / prime) > 1 {
                                                         format!("^{}", n / prime)
                                                     } else {
                                                         String::new()
                                                     },
                                                     if root_b > 1 {
                                                         format!("*{}", root_b)
                                                     } else {
                                                         String::new()
                                                     },
                                                     if root_c != 0 {
                                                         format!("{:+}", root_c)
                                                     } else {
                                                         String::new()
                                                     }).into());
                            }
                        }
                    }
                }
                3 => { // raw number
                    if let Ok(num) = expr.parse::<u128>() {
                        factors.extend(factorize128(num).keys().map(|k| k.to_string().into()));
                    } else {
                        factors.push(expr.into());
                    }
                }
                4 => { // parens
                    factors.extend_from_slice(&self.find_factors(&captures[1]));
                }
                5 => { // division by a raw number
                    let numerator = self.find_factors(&captures[1]);
                    let Ok(divisor) = captures[2].parse::<u128>() else {
                        warn!("Could not parse divisor: {}", &captures[2]);
                        return numerator;
                    };
                    let mut numerator = numerator.into_iter().collect::<HashSet<CompactString>>();
                    if !numerator.remove(&CompactString::from(divisor.to_string())) {
                        for other_factor in numerator.clone().into_iter() {
                            if let Ok(other_num) = other_factor.parse::<u128>() {
                                let gcd = divisor.gcd(&other_num);
                                if gcd > 1 {
                                    numerator.remove(&other_factor);
                                    if other_num / gcd > 1 {
                                        numerator.insert((other_num / gcd).to_string().into());
                                    }
                                }
                            }
                        }
                    }
                    factors.extend(numerator.into_iter());
                }
                6 => { // division by another expression
                    let numerator = self.find_factors(&captures[1]).into_iter().collect::<HashSet<CompactString>>();
                    let denominator = self.find_factors(&captures[2]).into_iter().collect::<HashSet<CompactString>>();
                    factors.extend(numerator.difference(&denominator).cloned());
                }
                7 => { // multiplication
                    for term in [&captures[1], &captures[2]] {
                        let term_factors = self.find_factors(term);
                        if term_factors.is_empty() {
                            factors.push(term.into());
                        } else {
                            factors.extend_from_slice(&term_factors);
                        }
                    }
                }
                _ => unsafe { unreachable_unchecked() }
            }
        }
        factors.sort();
        factors.dedup();
        if factors.is_empty() {
            warn!("No factors found for expression {expr}");
        } else {
            info!("Found factors of expression {expr}: {}", factors.iter().join(", "));
        }
        factors.into_boxed_slice()
    }
}