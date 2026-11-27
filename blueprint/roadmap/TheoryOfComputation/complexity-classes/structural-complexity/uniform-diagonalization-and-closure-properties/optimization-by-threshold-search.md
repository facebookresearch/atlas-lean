# Optimization by binary search with an NP oracle

Let an NP optimization problem have, on every instance $x$, a nonempty set of feasible solutions, all of length at most $p(|x|)$ for a fixed polynomial $p$, and integer objective values in $[0,B(x)]$ with $\log B(x)$ polynomially bounded, and let the threshold language $\{(x,k): \exists y\text{ feasible with value}\ge k\}$ be in $\mathsf{NP}$. Then the optimum value is computable in polynomial time with $\lceil\log_2(B(x)+1)\rceil$ queries to that threshold language, and an optimal solution is then computable in $\mathsf{FP}^{\mathsf{NP}}$ by self-reduction at the optimal threshold.

## Proof sketch

Bisect the interval of candidate thresholds; the number of steps equals the bit length of the interval. At the optimum $k^*$, fix the solution bit by bit while keeping 'some solution of value $\ge k^*$ extends this prefix' true.

## Depends on

- [Polynomial time with an oracle](../../time-and-space-complexity-classes/pwith-oracle.md)
- [The complexity class NP](../../the-classes-p-np-and-conp/np.md)
- [NPO optimization problems](../../time-and-space-complexity-classes/is-npo.md)

## Proof depends on

- [Search reduces to decision: FP-search = FNP iff P = NP](../../total-search-problems/tfnp-subclasses/search-to-decision.md)

## Sources

- Christos H. Papadimitriou, "Computational Complexity", Addison-Wesley, 1994, Section 17.1.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
