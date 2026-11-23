# The permanent is #P-complete (Valiant)

The function that sends a bitstring encoding a
square 0-1 matrix to its permanent, and every other bitstring to $0$, is $\#P$-complete.

Here $\#P$-completeness is with respect to polynomial-time oracle (Turing) reductions, as in
Valiant's definition: a function $y$ is $\#P$-complete when $y \in \#P$ and $\#P \subseteq FP^{y}$.
Completeness under parsimonious reductions would fail unless $P = NP$, because deciding whether a
0-1 permanent is nonzero (whether a bipartite graph has a perfect matching) is in polynomial time.

## Informally uses

- [Counting SAT is #P-complete](../counting-satisfiability-sat/count-sat-sharp-p-complete.md):
  Valiant's proof reduces counting the satisfying assignments of a CNF formula to the permanent
  (his Lemma 3.1: $\operatorname{per} f(F) = 4^{t(F)} s(F)$), and takes the $\#P$-hardness of
  counting satisfying assignments from a parsimonious form of Cook's construction (his Lemma 3.2).

## Background

- [The 0-1 permanent counts perfect matchings](permanent-boole-eq-card.md): the reading of this
  theorem as the $\#P$-completeness of counting perfect matchings in bipartite graphs.
- [General matching is in P (Edmonds' blossom algorithm)](../../polynomial-time-problems/matching-in-general-graphs/matching-in-p.md):
  the decision counterpart is in polynomial time, which is what makes this completeness result
  surprising.

## Sources

- L. G. Valiant, "The complexity of computing the permanent", Theoretical Computer Science 8 (1979), 189-201, Theorem 1; Section 2 (definition of $\#P$-completeness by oracle reductions); Section 3, Lemmas 3.1-3.3.
