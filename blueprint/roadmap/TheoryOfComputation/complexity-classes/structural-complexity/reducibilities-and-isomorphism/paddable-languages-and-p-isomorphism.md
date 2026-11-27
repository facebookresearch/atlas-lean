# Paddable languages and polynomial-time isomorphism

Languages $A,B$ are **p-isomorphic** if there is a bijection $h$ of instances with $h$ and $h^{-1}$ polynomial-time computable and $x\in A\iff h(x)\in B$. $A$ is **paddable** if there is a polynomial-time map $\mathrm{pad}(x,y)$ with $\mathrm{pad}(x,y)\in A\iff x\in A$, together with a polynomial-time decoder recovering $y$ from $\mathrm{pad}(x,y)$. The **Berman–Hartmanis conjecture** states that all $\mathsf{NP}$-complete languages are p-isomorphic; it holds iff every $\mathsf{NP}$-complete language is paddable, and it implies $\mathsf{P}\ne\mathsf{NP}$ (if $\mathsf{P}=\mathsf{NP}$, a finite set and an infinite co-finite set would both be NP-complete).

## Depends on

- [Transitivity of polynomial-time many-one reductions](../../../np-completeness/satisfiability/3-satisfiability/poly-many-one-red-trans.md)
- [NP-complete decision problems](../../mahaney-s-theorem/npcomplete.md)

## Sources

- Leonard Berman and Juris Hartmanis, "On Isomorphisms and Density of NP and Other Complete Sets", SIAM Journal on Computing 6(2), 1977.
