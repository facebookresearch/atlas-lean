# Ilango–Ren–Santhanam: one-way functions exist iff GapMCSP is average-case hard on some locally samplable distribution

With $N$ the truth-table length, the following are equivalent:

1. One-way functions exist.
2. For some constant $\delta>0$ and some $s=\Omega(N^{\delta})$ there is an $N^{\delta}$-locally samplable distribution $\mathcal D$ such that $\mathrm{GapMCSP}[s,\ s\cdot N^{5\delta}]$ is weakly average-case hard on $\mathcal D$.
3. For every constant $\delta>0$ there is an $N^{\delta}$-locally samplable distribution $\mathcal D$ such that $\mathrm{GapMCSP}[N^{\delta},\ o(N/\log N)]$ is strongly average-case hard on $\mathcal D$.

This is the first unconditional characterization of one-way functions by the average-case hardness of MCSP; it is robust in the size threshold, the approximation gap and the error tolerance.

## Proof sketch

Item 1 implies item 3: a pseudorandom function family yields an $N^{\delta}$-locally samplable distribution of truth tables of circuit complexity at most $N^{\delta}$ that is indistinguishable from uniformly random truth tables, which have circuit complexity $\Omega(N/\log N)$ with high probability. Item 3 implies item 2 trivially. Item 2 implies item 1 via the generic coding-theorem argument, using a coding theorem for circuit complexity under locally samplable distributions; because that coding theorem is not tight and circuit size is not additive enough, a multiplicative gap $N^{5\delta}$ replaces the additive gap.

## Depends on

- [GapMCSP[s,c], GapK[s,c] and weak versus strong average-case hardness on a distribution](gap-meta-complexity-and-weak-strong-average-case-hardness.md)
- [One-way functions exist](../impagliazzo-s-five-worlds/owfexists.md)
- [Locally samplable distributions on truth tables](locally-samplable-distributions.md)

## Proof depends on

- [Ilango–Ren–Santhanam: a coding theorem plus average-case hardness of additive approximation yields one-way functions](irs-coding-theorem-plus-hardness-gives-owf.md)
- [Pseudorandom generators exist if and only if one-way functions exist](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-generators/pseudorandom-generators-exist-if-and-only-if.md)
- [Razborov-Rudich: the natural proofs barrier](../../hierarchy-theorems-and-barriers/natural-proofs-barrier/razborov-rudich-natural-proofs.md)

## Sources

- Rahul Ilango, Hanlin Ren and Rahul Santhanam, "Robustness of Average-Case Meta-Complexity via Pseudorandomness", STOC (2022).
