# Oliveira–Santhanam: pseudodeterministic polynomial-time hitting sets or deterministic subexponential ones

For each constant $c>0$ at least one of the following holds.

1. There is a pseudodeterministic polynomial-time construction of a family $\{H_n\}$, $H_n\subseteq\{0,1\}^n$, such that for every $(1/n^{c})$-dense property $Q\in\mathrm{DTIME}(n^{c})$ and every large enough $n$, $H_n\cap Q_n\neq\emptyset$.
2. There is a deterministic subexponential-time construction of a family $\{H'_n\}$, $H'_n\subseteq\{0,1\}^n$, such that for every $(1/n^{c})$-dense $Q\in\mathrm{DTIME}(n^{c})$ and infinitely many $n$, $H'_n\cap Q_n\neq\emptyset$.

## Proof sketch

The argument is a win-win over the Trevisan–Vadhan language $L_{\mathrm{TV}}$, which is $\mathrm{PSPACE}$-complete, downward self-reducible and randomly self-reducible. If $L_{\mathrm{TV}}\in\mathrm{BPP}$ then $\mathrm{PSPACE}\subseteq\mathrm{BPP}$, and the lexicographically first suitable set (found by polynomial-space search) is produced pseudodeterministically. Otherwise the uniform hardness-randomness tradeoff of Trevisan–Vadhan gives, infinitely often, a subexponential-time computable pseudorandom set fooling $n^{c}$-time tests, which therefore intersects every dense easy property.

## Depends on

- [Pseudodeterministic constructions for dense properties, everywhere and infinitely often](pseudodeterministic-construction-of-dense-property.md)

## Proof depends on

- [Impagliazzo-Wigderson: exponential circuit hardness in E derandomizes BPP](../../../pseudorandomness-and-one-way-functions/nisan-wigderson.md)

## Sources

- Igor C. Oliveira and Rahul Santhanam, "Pseudodeterministic Constructions in Subexponential Time", STOC (2017), ECCC TR16-196.
- Lijie Chen, Zhenjian Lu, Igor C. Oliveira, Hanlin Ren and Rahul Santhanam, "Polynomial-Time Pseudodeterministic Construction of Primes", FOCS (2023), arXiv:2305.15140.
