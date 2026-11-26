# The Oliveira–Santhanam formula magnification construction is local

For $n \le s(n)$ and $\delta(n) > 0$, approximate MCSP $\big[(s, 0), (s, \delta)\big]$ on $N = 2^n$-bit truth tables is computed by De Morgan formulas with at most $N$ oracle gates to a single fixed oracle (an encoding of Succinct MCSP), each of fan-in at most $98\,\big(\lceil 1/\delta \rceil (s + 1)\big)^3$, adaptivity $1$, and $N$ times that many input leaves. Hence the formula lower bounds required by Oliveira–Santhanam magnification cannot be proved by techniques that also apply to such local oracle formulas.

## Proof sketch

Each oracle gate receives a random sample of $O(s/\delta)$ truth-table positions with their values (hard-wired leaves) and asks the Succinct MCSP oracle whether a circuit of size $s$ fits; a no-instance is rejected by most samples, and an AND over $N$ independent samples amplifies.

## Depends on

- [Oracle circuits and local circuit classes](oracle-circuits-and-local-circuit-classes.md)
- [Approximate MCSP](approximate-mcsp.md)
- [Succinct MCSP](../minimum-circuit-size-problem/succinct-mcsp.md)

## Proof depends on

- [Oliveira–Santhanam: formula lower bounds for approximate MCSP above N polylog N give NP ⊄ Formula[poly]](oliveira-santhanam-formula-magnification.md)

## Sources

- L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal and R. Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality", ITCS 2020.
- I. C. Oliveira and R. Santhanam, "Hardness Magnification for Natural Problems", FOCS 2018.
