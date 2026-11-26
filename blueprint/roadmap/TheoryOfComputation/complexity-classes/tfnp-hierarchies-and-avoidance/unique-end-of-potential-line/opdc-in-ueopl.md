# OPDC lies in UEOPL under promise-preserving reductions via a surface-walking line with a lexicographic potential

There is a polynomial-time promise-preserving reduction from OPDC to UNIQUE-EOPL. In particular OPDC is total, and a violation-free OPDC instance has a unique solution, found by following the unique line of the produced instance.

## Proof sketch

First reduce to UNIQUE-FORWARD-EOPL (successor circuit only; solutions are sinks or potential failures, violations are pairs with equal potentials or with $V(x)<V(y)<V(S(x))$). In two dimensions the line walks up a column until it meets the dimension-1 zero surface, then, if $D_2$ says up, steps right and restarts; potential $V(p)=k\,p_2+p_1$ increases lexicographically. A vertex is a pair $(p,q)$ where $q$ is the last surface point visited (with $D_2(q)=\mathrm{up}$ and $q_2=p_2-1$), which rules out false lines beyond the fixpoint; stuck columns give (OV2) or (OV3), and two surface points in one column give (UV3)-type pairs mapping to (OV1). The general case recurses over $i$-slices. Then pad potentials to increase by exactly one with dummy chains and apply the Hubáček–Yogev reduction from verifiable lines to metered lines, checking that every violation maps back.

## Depends on

- [One-Permutation Discrete Contraction (OPDC): direction functions on a grid with unique fixpoints on i-slices](one-permutation-discrete-contraction.md)
- [UNIQUE-EOPL, the class UEOPL and PromiseUEOPL: one potential line certified by violation solutions](unique-eopl-and-ueopl.md)

## Proof depends on

- [Hubáček–Yogev: exponential randomized query lower bound and obfuscation-based hardness for continuous local search](continuous-local-search-query-and-crypto-lower-bounds.md)
- [END-OF-METERED-LINE and END-OF-POTENTIAL-LINE are polynomial-time equivalent, so EOPL is contained in CLS](end-of-metered-line-equivalent-to-eopl.md)

## Sources

- John Fearnley, Spencer Gordon, Ruta Mehta and Rahul Savani, "Unique End of Potential Line", ICALP (2019), arXiv:1811.03841.
- Pavel Hubáček and Eylon Yogev, "Hardness of Continuous Local Search: Query Complexity and Cryptographic Lower Bounds", SODA (2017) and SIAM Journal on Computing (2020), ECCC TR16-063.
