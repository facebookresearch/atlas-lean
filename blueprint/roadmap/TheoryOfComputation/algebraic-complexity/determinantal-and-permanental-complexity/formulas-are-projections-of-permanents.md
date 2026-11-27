# Arithmetic formulas are projections of the permanent

Over every commutative ring $K$, a polynomial computed by an arithmetic formula (fan-in two) with $s$ addition and multiplication gates (input leaves free) is a projection of the generic $(s+1)\times(s+1)$ permanent. Moreover, if $M$ is a $d\times d$ matrix of variables and constants in which a variable $y$ occurs in exactly one entry, then $\sum_{b\in\{0,1\}}\mathrm{per}(M|_{y=b})$ is a projection of the $(d+1)\times(d+1)$ generic permanent.

## Proof sketch

The branching program of the formula, with source and sink identified and loops of weight one at the other vertices, has exactly one cycle cover per source-to-sink path, and the permanent counts these without signs. For the selector, write $\mathrm{per}(M)=y\,g_1+g_0$ with $g_0,g_1$ free of $y$, so the sum over $b$ is $g_1+2g_0$: subdivide the edge carrying $y$ by a new vertex with a loop of weight $2$ (the edge's two halves get weight $1$), so that cycle covers using the old edge keep their weight with $y=1$ and all others pick up the factor $2$.

## Depends on

- [Specialization matrices and determinantal representations](specialization-matrices-and-determinantal-representations.md)
- [Permanent of an encoded 0-1 matrix](../../counting-complexity/complexity-of-the-permanent/perm-fun.md)

## Proof depends on

- [Valiant: arithmetic formulas are projections of linear-size determinants](formulas-are-projections-of-determinants.md)

## Sources

- Leslie G. Valiant, "Completeness Classes in Algebra", Proceedings of the Eleventh Annual ACM Symposium on Theory of Computing, 1979.
- Ian Orzel, Srikanth Srinivasan, Sébastien Tavenas, Amir Yehudayoff, "The Algebraic Cost of a Boolean Sum", 45th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science, 2025, Lemma 2 and Claim 11.
- Ramprasad Saptharishi, "A survey of lower bounds in arithmetic circuit complexity", version 9.0.3, 2021, Sections 3.3.1 and 3.3.4.
