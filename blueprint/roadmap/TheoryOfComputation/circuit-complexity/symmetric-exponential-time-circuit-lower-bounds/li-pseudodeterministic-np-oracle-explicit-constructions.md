# Li: zero-error pseudodeterministic NP-oracle constructions on every length for Ramsey graphs, rigid matrices, extractors and codes

For every input length there are zero-error pseudodeterministic constructions with an $\mathrm{NP}$ oracle (single-valued $\mathrm{FZPP}^{\mathrm{NP}}$ algorithms) for Ramsey graphs, rigid matrices, pseudorandom generators, two-source extractors, linear codes, hard truth tables and $\mathrm{K}^{\mathrm{poly}}$-random strings, each with the parameters given by the probabilistic method. Also, for $m=2^{\Omega(n)}$, the problem of outputting an $n$-bit string missing from a list of $m<2^n$ strings is solvable by a uniform family of $2^{\mathrm{poly}(n)}$-size depth-3 $\mathrm{AC}^0$ circuits.

## Proof sketch

Each listed construction problem reduces to Avoid, so composing the reduction with the single-valued $\mathrm{FZPP}^{\mathrm{NP}}$ algorithm for Avoid gives canonical outputs. The missing-string statement follows from a theorem of Vyas and Williams that it is equivalent to relativized $2^{\Omega(n)}$ circuit lower bounds for $\Sigma_2\mathrm{E}$, which hold by the relativizing almost-everywhere lower bound.

## Depends on

- [Single-valued FΣ2P and FS2P algorithms for search problems](single-valued-fsigma2p-and-fs2p.md)
- [Pseudorandom generators against circuits](../../pseudorandomness-and-one-way-functions/derandomization/pseudorandom-generators-against-circuits.md)

## Proof depends on

- [Li: a single-valued FS2P algorithm solves Avoid on every input length](li-single-valued-fs2p-avoid.md)
- [Probabilistic-method explicit constructions reduce to Avoid](../../complexity-classes/tfnp-hierarchies-and-avoidance/range-avoidance-and-explicit-constructions/explicit-constructions-in-apepp.md)
- [Li: S2E is not in i.o.-SIZE[2^n/n], giving almost-everywhere bounds for Σ2E ∩ Π2E and ZPE^NP](li-s2e-almost-everywhere-lower-bound.md)

## Sources

- Zeyong Li, "Symmetric Exponential Time Requires Near-Maximum Circuit Size: Simplified, Truly Uniform", STOC (2024), arXiv:2310.17762.
