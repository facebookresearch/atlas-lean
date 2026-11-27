# The Oliveira–Santhanam formula magnification construction is local

For every constructive $s(n)$ with $n \le s(n) \le 2^n/\mathrm{poly}(n)$ and every $0 < \delta(n) < 1/2$, approximate MCSP $\big[(s, 0), (s, \delta)\big]$ on $N = 2^n$-bit truth tables is computed by De Morgan formulas of size $N \cdot \mathrm{poly}(s/\delta)$ with at most $N$ oracle gates to a single fixed oracle, each of fan-in $\mathrm{poly}(s/\delta)$, and adaptivity $1$; that is, it lies in $[N, \mathrm{poly}(s/\delta), 1]\text{-}\mathrm{Formula}[N \cdot \mathrm{poly}(s/\delta)]$ (Chen et al. 2020, Proposition 63 in the full version). Hence the formula lower bounds required by Oliveira–Santhanam magnification cannot be proved by techniques that also apply to such local oracle formulas.

## Proof sketch

Each oracle gate receives a random sample of $\mathrm{poly}(s/\delta)$ truth-table positions with their values (hard-wired leaves) and asks the Succinct MCSP oracle whether a circuit of size $s$ fits; a no-instance is rejected by most samples, and an AND over $N$ independent samples amplifies.

## Depends on

- [Oracle circuits and local circuit classes](oracle-circuits-and-local-circuit-classes.md)
- [Approximate MCSP](approximate-mcsp.md)
- [Succinct MCSP](../minimum-circuit-size-problem/succinct-mcsp.md)

## Proof depends on

- [Oliveira–Santhanam: formula lower bounds for approximate MCSP above N polylog N give NP ⊄ Formula[poly]](oliveira-santhanam-formula-magnification.md)

## Sources

- L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal and R. Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality", ITCS 2020; full version arXiv:1911.08297, Appendix A.2, Proposition 63.
- I. C. Oliveira and R. Santhanam, "Hardness Magnification for Natural Problems", FOCS 2018.
