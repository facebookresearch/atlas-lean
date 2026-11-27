# Valiant's reduction needs negative entries unless P = NP

If $\mathsf{P}\ne\mathsf{NP}$, there are no nonzero integer $c$, set $I\subseteq\mathbb{Z}_{\ge0}$ and polynomial-time map $\varphi\mapsto M_\varphi$ into matrices with entries in $I$ such that $\operatorname{perm}(M_\varphi)=c^{m}\cdot\#\varphi$ for every 3-CNF formula $\varphi$ with $m$ clauses.

## Proof sketch

For nonnegative matrices, $\operatorname{perm}(M)>0$ iff the bipartite graph of the nonzero entries has a perfect matching, which is decidable in polynomial time; such a reduction would therefore decide satisfiability.

## Depends on

- [The 0-1 permanent counts perfect matchings](../complexity-of-the-permanent/permanent-boole-eq-card.md)
- [The complexity class P](../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Cook–Levin theorem: SAT is NP-complete](../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercise 6.25.
