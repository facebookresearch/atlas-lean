# Bodlaender–Jansen–Kratsch: cross-composition rules out polynomial kernels

An **OR-cross-composition** of a language $A$ into a parameterized problem $(Q,\kappa)$ maps, in polynomial time, a list $x_1,\dots,x_t$ of instances of $A$ that are equivalent under a polynomial equivalence relation to an instance $y$ with $\kappa(y)\le\mathrm{poly}(\max_i|x_i|+\log t)$ and $y\in Q\iff\exists i\,x_i\in A$. If an $\mathsf{NP}$-hard language OR-cross-composes into $(Q,\kappa)$ and $(Q,\kappa)$ has a polynomial compression, then $\mathsf{coNP}\subseteq\mathsf{NP}/\mathrm{poly}$.

## Proof sketch

Composing the cross-composition with the compression gives an OR-distillation of $A$ (the polynomial equivalence relation lets one group instances into polynomially many classes first), and the Fortnow–Santhanam theorem applies.

## Depends on

- [Kernelization and polynomial compression](kernelization.md)

## Proof depends on

- [Fortnow–Santhanam: OR-distillation implies coNP ⊆ NP/poly](or-distillation.md)

## Sources

- Hans L. Bodlaender, Bart M. P. Jansen and Stefan Kratsch, "Kernelization Lower Bounds by Cross-Composition", SIAM Journal on Discrete Mathematics 28(1), arXiv:1206.5941, 2014, Definition 9, Theorem 5 and Corollary 2.
