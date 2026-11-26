# Search reduces to decision: FP-search = FNP iff P = NP

Every search problem $R\in\mathsf{FNP}$ is solved in polynomial time with access to its prefix decision problem $\{(x,u):\exists y\,(x,uy)\in R\}\in\mathsf{NP}$ by extending a witness one bit at a time. Consequently every search problem in $\mathsf{FNP}$ is solvable in polynomial time if and only if $\mathsf{P}=\mathsf{NP}$.

## Proof sketch

Ask whether $(x,u0)$ or $(x,u1)$ extends to a witness and follow a 'yes' branch; after polynomially many queries a full witness is found and checked. Conversely, a polynomial-time solver for the SAT relation decides SAT.

## Depends on

- [Search problems: FNP, FP and TFNP](../search-problems-fnp-fp-and-tfnp.md)
- [The complexity class P](../../the-classes-p-np-and-conp/p.md)
- [The complexity class NP](../../the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Cook–Levin theorem: SAT is NP-complete](../../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Sources

- Christos H. Papadimitriou, "Computational Complexity", Addison-Wesley, 1994, Section 10.3.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009, Section 2.5.
