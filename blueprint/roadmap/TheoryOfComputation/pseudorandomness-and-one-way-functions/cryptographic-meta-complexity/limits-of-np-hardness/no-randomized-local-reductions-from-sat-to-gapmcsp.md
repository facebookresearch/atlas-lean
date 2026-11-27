# Ilango–Ren–Santhanam: NC0 one-way functions rule out randomized local reductions from SAT to GapMCSP

If one-way functions computable in $\mathsf{NC}^0$ exist, then for every $\delta>0$ and $s=\Omega(n^{\delta})$ there is no randomized $(n^{\delta})$-local reduction from SAT to GapMCSP$[s,s\,n^{4\delta}]$: the first evidence against randomized reductions from SAT to GapMCSP.

**Theorem.** Suppose there are one-way functions computable in $\mathsf{NC}^0$. Then for each $\delta>0$ and $s=\Omega(n^{\delta})$, there are no randomized $(n^{\delta})$-local reductions from SAT to GapMCSP$[s,s\,n^{4\delta}]$.

Here $n$ is the length of the GapMCSP input (the truth table), GapMCSP$[s,c]$ asks to distinguish truth tables of circuit complexity at most $s$ from those of circuit complexity at least $c$, and an $(n^{\delta})$-local reduction computes each output bit within time $n^{\delta}$ with random access to its input and randomness, in the same sense as $t$-local samplers. Murray and Williams had ruled out deterministic local reductions unconditionally; this result handles randomized ones under a cryptographic assumption.

## Expansion

First, if a language $L$ has randomized local reductions to GapMCSP, then $L$ is easy on average over every locally samplable distribution: GapMCSP is easy on average over a locally samplable distribution when the algorithm sees the sampler's randomness rather than only its output, because truth tables of high circuit complexity are sampled with low probability by a local sampler (the circuit-complexity coding theorem used for the one-way-function characterization of GapMCSP). Second, one-way functions in $\mathsf{NC}^0$ make $k$-SAT average-case hard on some locally samplable distribution. Composing the two contradicts the existence of the reduction.

## Depends on

- [GapMCSP[s,c], GapK[s,c] and weak versus strong average-case hardness on a distribution](../../worst-case-characterizations-of-one-way-functions/gap-meta-complexity-and-weak-strong-average-case-hardness.md)
- [Locally samplable distributions on truth tables](../../worst-case-characterizations-of-one-way-functions/locally-samplable-distributions.md)
- [Cook–Levin theorem: SAT is NP-complete](../../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Proof depends on

- [Ilango–Ren–Santhanam: one-way functions exist iff GapMCSP is average-case hard on some locally samplable distribution](../../worst-case-characterizations-of-one-way-functions/irs-owf-iff-gapmcsp-hard-on-local-distribution.md)

## Sources

- Rahul Ilango, Hanlin Ren and Rahul Santhanam, "Robustness of Average-Case Meta-Complexity via Pseudorandomness", *54th Annual ACM Symposium on Theory of Computing (STOC 2022)*, 2022, https://doi.org/10.1145/3519935.3520051 (Theorem 2.8, Section 3).
