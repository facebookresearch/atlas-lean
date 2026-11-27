# Phased hinted lower-bound predicates fail below $1/18$

Let $\tau_0$ be the cutoff indicated below. In this restricted word RAM, for each $0<\tau<\tau_0$ and every real $\omega\ge2$, there is an $\eta>0$ for which a phased algorithm achieves phase-2 and phase-3 exponents at most $(\omega-\eta,1+\tau-\eta)$ for the vector-hinted problem, and likewise for the matrix-vector-hinted problem (the saving and program may differ). For every $0<\tau_1<\tau_0\tau_2$ with $\tau_2<1$ and every real $\omega_2\ge2$, $\omega_3\ge1+\tau_2$, some $\eta>0$ is attainable with phase exponents $(\omega_2-\eta,\omega_3-\eta,\tau_1+\tau_2-\eta)$ for the vector-matrix-vector problem. All first phases are polynomial. This is the negation of the phased lower-bound predicates for **arbitrary real** candidate exponents satisfying the stated constraints, not a statement establishing bounds on actual rectangular matrix multiplication exponents. Here $\tau_0=1/18$.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Phased Boolean products](../machine-and-inputs/three-hinted-boolean-products.md)
- [Decay and entropy parameters](../machine-and-inputs/thin-product-decay-parameters.md)

## Proof depends on

- [Phased algorithms giving the saving](fixed-saving-for-thin-hints.md)

## Proof outline

Formalize the matrix block construction and its correctness across phases; verify time in each phase without using input supplied later.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L4110-L4127); [ThreeSumApsp.wordRam_corollary_40_fail](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L238-L242), [ThreeSumApsp.wordRam_theorem_4](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L260-L262).
