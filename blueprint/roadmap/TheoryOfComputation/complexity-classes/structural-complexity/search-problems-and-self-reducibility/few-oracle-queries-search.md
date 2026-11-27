# Logarithmically many oracle queries do not help solve PC search problems

Let $R\in\mathsf{PC}$ and suppose its search problem is solved in polynomial time by an oracle machine (with any oracle language) that makes at most $c\log_2 n+c$ queries on inputs of length $n$. Then $R\in\mathsf{PF}$. More generally the same holds for any query bound $r(n)$ with $2^{r(n)}$ polynomially bounded.

## Proof sketch

Run the oracle machine for all $2^{r(n)}=\mathrm{poly}(n)$ possible answer sequences and check each candidate output with the polynomial-time decider of $R$; the true answer sequence yields a correct solution, and checking filters out wrong ones.

## Depends on

- [Self-reducible search problems (Goldreich's PC and PF)](self-reducible-search-problems.md)
- [Bounded-query oracle classes and P^{NP[O(log n)]}](../advice-sparse-and-selective-sets/bounded-query-classes.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercise 2.10.
