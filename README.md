## This is not a useless DDoS tool

The scripts in this repository serve to:

* Factor composite numbers of 80-89 digits in GitHub Actions, and of up to 106 digits when running on my laptop.
* Request of the factordb.com server that it make its limited on-demand efforts (P-1/P+1 (Pollard's rho?) and 10 ECM curves) to factor larger composites.
* Request PRP checks and N-1/N+1 proof attempts for numbers whose current status is PRP. (NB: proofs of this kind cannot be uploaded.)
* Request PRP checks for numbers whose current status is U. (These can't be uploaded either, except when they yield a factor.)
* Put the results of all these calculations into the public record, decreasing the number of unfinished entries (PRP/U/C) on factordb.com.
