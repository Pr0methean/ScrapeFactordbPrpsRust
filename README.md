## Finishing the unfinished entries on FactorDB

The programs in this repository help the field of pure mathematics by factorizing large integers or establishing that they're prime numbers, and submitting the results to factordb.com to be stored. You can run them on GitHub Actions and/or your own computer (currently tuned for Linux x86-64). The ways they will help for a given number depend on its current status on factordb.com.

### Probable prime (PRP, 300 digits or larger)

* Request an N-1/N+1 combined proof attempt for the number. This can confirm or disconfirm its primality.
* Request Lucas probable-prime checks to all available bases (2 through 255). This can't confirm primality, but will almost always disconfirm it if the "probable prime" is actually composite.

### Composite (C, 91 to 300 digits)

* Request server-side attempts (P-1/P+1/ECM) to find factors.
* When not all factors are found this way, run [yafu](https://github.com/bbuhrow/yafu) on the GitHub Actions runner to find more. This doesn't always succeed because a GitHub Actions job can only run for 6 hours; but we improve our chances by:
** using 2 threads
** uploading partial results when we're close to the 6-hour limit

### Unknown status (U, 2001 to over 200,000 digits)
* When the last digit of an unknown-status number is displayed and is divisible by 2 and/or 5, report those factors.
* When it is listed as having algebraic factors, report those factors.
* For numbers up to 199,999 digits to which neither of the above apply, request the server to perform a probable-prime check (which, if the number is composite, often reveals small factors).
