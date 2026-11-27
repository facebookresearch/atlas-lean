# Fortnow–Santhanam: OR-distillation implies coNP ⊆ NP/poly

A (weak) **OR-distillation** of $A$ into $B$ maps a list $x_1,\dots,x_t$ of instances of $A$ in polynomial time to one instance $y$ of $B$ of length $\mathrm{poly}(\max_i|x_i|)$ (independent of $t$) with $y\in B\iff\exists i\ x_i\in A$. If an $\mathsf{NP}$-hard language has an OR-distillation into any language, then $\mathsf{coNP}\subseteq\mathsf{NP}/\mathrm{poly}$, and hence $\mathsf{PH}=\Sigma_3^p$.

## Proof sketch

Fix a length $n$ and $t=\mathrm{poly}(n)$. Each no-instance $y$ of $B$ of the output length 'covers' the tuples of no-instances of $A$ mapped to it; by counting, polynomially many such $y$ cover all no-instances of $A$ of length $n$ in the sense that $x\notin A$ iff some tuple containing $x$ maps to one of them. These $y$ form advice for an NP verifier of $\overline{A}$.

## Depends on

- [Kernelization and polynomial compression](kernelization.md)
- [NP/poly](../../structural-complexity/boolean-hierarchy-and-polynomial-hierarchy-collapses/np-with-polynomial-advice.md)

## Proof depends on

- [Yap: coNP ⊆ NP/poly collapses PH to Σ₃](../../structural-complexity/boolean-hierarchy-and-polynomial-hierarchy-collapses/yap-conp-in-np-poly.md)

## Sources

- Lance Fortnow and Rahul Santhanam, "Infeasibility of Instance Compression and Succinct PCPs for NP", Journal of Computer and System Sciences 77(1), 2011, Theorem 1.2 (stated for SAT; a Karp reduction from SAT to any NP-hard language transfers it).
- Hans L. Bodlaender, Bart M. P. Jansen and Stefan Kratsch, "Kernelization Lower Bounds by Cross-Composition", SIAM Journal on Discrete Mathematics 28(1), arXiv:1206.5941, 2014.
