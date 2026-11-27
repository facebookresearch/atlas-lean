# k-Path has no polynomial kernel unless coNP ⊆ NP/poly

The problem $k$-Path (does a graph contain a simple path on $k$ vertices?), parameterized by $k$, has no polynomial kernel and no polynomial compression unless $\mathsf{coNP}\subseteq\mathsf{NP}/\mathrm{poly}$ (and then $\mathsf{PH}=\Sigma_3^p$).

## Proof sketch

Hamiltonian Path OR-cross-composes into $k$-Path (instances are grouped by their number of vertices, a polynomial equivalence relation): given $t$ graphs on $n$ vertices, their disjoint union has a path on $n$ vertices iff one of them is Hamiltonian, and the parameter is $n$.

## Depends on

- [Kernelization and polynomial compression](kernelization.md)

## Proof depends on

- [Bodlaender–Jansen–Kratsch: cross-composition rules out polynomial kernels](cross-composition-kernel-lower-bounds.md)

## Sources

- Hans L. Bodlaender, Rodney G. Downey, Michael R. Fellows and Danny Hermelin, "On Problems without Polynomial Kernels", Journal of Computer and System Sciences 75(8), 2009.
- Hans L. Bodlaender, Bart M. P. Jansen and Stefan Kratsch, "Kernelization Lower Bounds by Cross-Composition", SIAM Journal on Discrete Mathematics 28(1), arXiv:1206.5941, 2014.
