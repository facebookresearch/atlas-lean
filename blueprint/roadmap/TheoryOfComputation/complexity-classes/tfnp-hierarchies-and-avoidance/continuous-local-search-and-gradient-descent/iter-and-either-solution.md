# ITER and the EITHER-SOLUTION combinator for building PPAD ∩ PLS-complete problems

**ITER.** Input: a Boolean circuit $C:[2^n]\to[2^n]$ with $C(v)\ge v$ for all $v$ and $C(1)>1$ (the inequality can be enforced syntactically by replacing $C(v)$ by $\max(C(v),v)$). Output: $v$ with $C(v)>v$ and $C(C(v))=C(v)$. Thinking of $[2^n]$ as a line, every node is a fixed point of $C$ or jumps to the right, and a solution is a non-fixed node mapped to a fixed node; one exists since the orbit of $1$ increases until it stabilizes. ITER is PLS-complete.

**END-OF-LINE** (recalled): circuits $S,P$ on $[2^n]$ define a graph of in- and out-degree at most one with source $1$; find a sink or a source other than $1$.

**EITHER-SOLUTION(A,B).** For search problems $A,B$: input a pair $(I_A,I_B)$ of instances; output a solution of $I_A$ or a solution of $I_B$.

## Depends on

- [END-OF-THE-LINE is total](../../../completeness-other-classes/ppad-and-the-end-of-the-line-problem/exists-solution.md)
- [The class PLS of polynomial local search problems](../../total-search-problems/the-class-pls-of-polynomial-local-search.md)

## Sources

- John Fearnley, Paul W. Goldberg, Alexandros Hollender and Rahul Savani, "The Complexity of Gradient Descent: CLS = PPAD ∩ PLS", STOC (2021) and Journal of the ACM 70(1) (2023), arXiv:2011.01929.
