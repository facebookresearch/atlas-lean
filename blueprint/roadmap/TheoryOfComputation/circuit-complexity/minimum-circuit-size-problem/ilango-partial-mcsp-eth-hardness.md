# Ilango: Partial MCSP requires N^{Ω(log log N)} time under ETH

Assume the Exponential Time Hypothesis. Then Partial MCSP on $m$-variable partial truth tables (with $N = 2^m$ entries) is not decidable by deterministic algorithms in time $2^{o(m \log m)} = N^{o(\log\log N)}$, for unary or binary size thresholds and for the De Morgan or binary-gate size measures.

## Proof sketch

Reduce from Bipartite Permutation Independent Set on $k \times k$ grids, which has no $2^{o(k \log k)}$ algorithm under ETH (Lokshtanov–Marx–Saurabh). Encode an instance as a partial function on $m = O(k)$-bit inputs whose small extensions are exactly monotone read-once formulas corresponding to permutations avoiding the forbidden pairs, so that the size threshold is met iff an independent permutation exists.

## Depends on

- [Partial MCSP (MCSP*)](partial-minimum-circuit-size-problem.md)
- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](../../fine-grained-complexity/fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md)

## Sources

- R. Ilango, "Constant Depth Formula and Partial Function Versions of MCSP are Hard", FOCS 2020.
