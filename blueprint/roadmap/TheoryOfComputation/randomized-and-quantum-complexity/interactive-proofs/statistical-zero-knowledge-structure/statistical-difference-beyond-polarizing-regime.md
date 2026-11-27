# Berman–Degwekar–Rothblum–Vasudevan: statistical difference beyond the polarizing regime α² ≤ β < α

Recall the Sahai–Vadhan polarization lemma: given circuits $(C_0,C_1)$ and $k$, one efficiently obtains $(D_0,D_1)$ with $\mathrm{SD}(D_0,D_1)\ge 1-2^{-k}$ if $\mathrm{SD}(C_0,C_1)\ge\alpha$ and $\mathrm{SD}(D_0,D_1)\le 2^{-k}$ if $\mathrm{SD}(C_0,C_1)\le\beta$, for constants with $\beta<\alpha^2$; the regime $\alpha^2\le\beta<\alpha$ is not known to polarize. Then:

1. there are polarization lemmas for triangular discrimination and Jensen–Shannon divergence that enable polarization for some instances whose statistical distance satisfies $\alpha^2<\beta<\alpha$, and polarization for statistical distance holds whenever $\alpha^2\ge\beta+1/\mathrm{poly}(n)$, an inverse-polynomial (not just constant) gap with $\beta$ below $\alpha^2$, provided the non-degeneracy conditions $2^{-n^{1/2-\varepsilon}}\le\beta(n)$ and $\alpha(n)\le 1-2^{-n^{1/2-\varepsilon}}$ hold for some constant $\varepsilon\in(0,1/2)$, where $\alpha,\beta$ may depend on the output length $n$ of the circuits;
2. for any $\beta<\alpha$ with $\alpha\ge\beta+1/\mathrm{poly}(n)$ (in particular for all constants $\beta<\alpha$), average-case hardness of $\mathrm{SD}^{\alpha,\beta}$ (deciding whether the statistical distance of two given circuits is at least $\alpha$ or at most $\beta$, on some samplable distribution of circuit pairs) implies the existence of one-way functions, previously known only for $\beta<\alpha^2$;
3. there is a direct constant-round interactive proof for estimating the statistical distance between two circuit-sampled distributions up to any inverse-polynomial additive error.

## Proof sketch

Triangular discrimination and Jensen–Shannon divergence are tied to statistical distance by $\mathrm{SD}^2\le\mathrm{TD}\le\mathrm{SD}$ and similar inequalities, and they behave well under direct products and XOR-type combinations, which yields polarization whenever the divergence gap survives; by the first inequality, this applies to statistical distance whenever $\alpha^2$ exceeds $\beta$ by an inverse polynomial. For item 2, if one-way functions do not exist then inverting the sampler on average lets one estimate, on most sampled pairs, the mutual information between a uniform selector bit and the corresponding sample, which is the Jensen–Shannon divergence of the pair, which separates $\mathrm{SD}\ge\alpha$ from $\mathrm{SD}\le\beta$ whenever $\alpha\ge\beta+1/\mathrm{poly}(n)$.

## Depends on

- [Promise-SZK and HVSZK: statistical zero-knowledge proofs for promise problems](promise-szk-and-hvszk.md)
- [One-way functions exist](../../../pseudorandomness-and-one-way-functions/impagliazzo-s-five-worlds/owfexists.md)
- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [One-way function families](../../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Sources

- Itay Berman, Akshay Degwekar, Ron D. Rothblum and Prashant Nalini Vasudevan, "Statistical Difference Beyond the Polarizing Regime", TCC (2019), ECCC TR19-038.
