# Self-reducible search problems (Goldreich's PC and PF)

For a relation $R\subseteq\{0,1\}^*\times\{0,1\}^*$ let $S_R=\{x:\exists y\,(x,y)\in R\}$. $R\in\mathsf{PC}$ ('polynomially checkable', the class $\mathsf{FNP}$) if $R$ is polynomially bounded and decidable in polynomial time; $R\in\mathsf{PF}$ if there is a polynomial-time function that, on every $x$, outputs some $y$ with $(x,y)\in R$ when $x\in S_R$ and a failure symbol otherwise. $R$ is **self-reducible** if its search problem is solvable in polynomial time with oracle access to the decision problem $S_R$; oracle access to the prefix-extension problem $\{(x,u):\exists v\,(x,uv)\in R\}$ always suffices for $R\in\mathsf{PC}$, so it is the decision problem $S_R$ that matters. SAT and every $\mathsf{NP}$-complete relation with the usual witness relation are self-reducible.

## Depends on

- [Search problems: FNP, FP and TFNP](../../total-search-problems/search-problems-fnp-fp-and-tfnp.md)
- [Polynomial-time computable functions](../../the-classes-p-np-and-conp/is-poly-time.md)
- [Polynomial time with an oracle](../../time-and-space-complexity-classes/pwith-oracle.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 0–2", 2006, Definitions 2.9 and 2.14.
