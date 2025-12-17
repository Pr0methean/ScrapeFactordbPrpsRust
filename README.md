## Finishing the unfinished entries on FactorDB

The programs in this repository help the field of pure mathematics by factorizing large integers or establishing that they're prime numbers, and submitting the results to factordb.com to be stored. You can run them on GitHub Actions and/or your own computer (currently tuned for Linux x86-64). The ways they will help for a given number depend on its current status on factordb.com.

### Probable prime (PRP, 300 to 200,000 digits)

* Factor N-1 and N+1 using:
** Logical deduction of factors of 2 and 3 (since all PRPs are equivalent to 1 or 5 mod 6).
** The same factor-finding methods used with unknown status (see below).
* Request an N-1/N+1 combined proof attempt for the number. This can confirm or disconfirm its primality.
* Request Lucas probable-prime checks to all available bases (2 through 255). This can't confirm primality, but will almost always disconfirm it if the "probable prime" is actually composite.

### Composite (C, 91 to 300 digits)

* Request server-side attempts (P-1/P+1/ECM) to find factors.
* When not all factors are found this way, run [yafu](https://github.com/bbuhrow/yafu) on the GitHub Actions runner to find more. This doesn't always succeed because a GitHub Actions job can only run for 6 hours; but we improve our chances by:
** using 4 threads
** uploading partial results when we're close to the 6-hour limit

### Unknown status (U, 2001 to over 200,000 digits)
* Reports factors detected by:
** like-powers factorization (a^x +/- b^x)
** last-digit check for factors of 2 and 5
** sum-of-digits check for factors of 3
** evaluation modulo small primes
** numeric factorization up to 128 bits
** algebraic factors listed in `frame_moreinfo.php`
** known factors of false detected factors
* For numbers up to 199,999 digits with no factors left to report, request the server to perform a probable-prime check (which often reveals small factors of a composite.
