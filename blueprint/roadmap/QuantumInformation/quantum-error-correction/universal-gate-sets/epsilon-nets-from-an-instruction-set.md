# Finite nets from an instruction set

Let $\mathcal{G}$ be an [instruction set](instruction-set.md) for $SU(d)$. For every $\varepsilon_0 > 0$ there is a length
$l_0$ such that the products $g_1 \cdots g_m$ of at most $l_0$ elements of $\mathcal{G}$ form an $\varepsilon_0$-net of
$SU(d)$: every $U \in SU(d)$ is within operator-norm distance $\varepsilon_0$ of one of them. The products of length at
most $l$ form an increasing sequence of finite sets whose union is dense in $SU(d)$, so the open balls of radius
$\varepsilon_0$ around them cover the compact group $SU(d)$, and finitely many suffice. These products are the basic
approximations at the bottom of the Solovay–Kitaev recursion.

## Depends on

- [Instruction set for $SU(d)$](instruction-set.md)

## Sources

- C. M. Dawson and M. A. Nielsen, *The Solovay–Kitaev algorithm*, Quantum Inf. Comput. 6 (2006), 81–95, arXiv:quant-ph/0505030, Section 3 (the preprocessing stage: "enumerating and storing a large number of instruction sequences from $G$ ... up to some sufficiently large (but fixed) length $l_0$") and Section 5.1 (the qudit case).
