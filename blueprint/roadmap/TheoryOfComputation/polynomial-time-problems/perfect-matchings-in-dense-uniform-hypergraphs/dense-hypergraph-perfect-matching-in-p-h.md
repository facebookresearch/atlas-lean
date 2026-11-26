# Perfect matchings in dense hypergraphs are decidable in polynomial time

For every natural number $k \ge 2$ and every rational $c$ with $1/k \le c < 1/2$, the decision
problem [$\mathrm{PM}(k, c)$](perfect-matching-problem.md) is in the complexity class P: the
positive answer to [Ruciński's question](dense-hypergraph-perfect-matching-in-p.md).

Keevash, Knox and Mycroft give a polynomial-time algorithm when the minimum codegree is at least
$n/k + \gamma n$ for a fixed $\gamma > 0$, and Han extends it to minimum codegree at least $n/k$,
which covers every $c$ with $1/k \le c < 1/2$. An algorithm can reject at once an input with fewer
edges than the codegree condition forces; on the remaining inputs $n$ is polynomial in the input
length.

## Sources

- Andrzej Ruciński, "Hamilton cycles and perfect matchings in hypergraphs", in *Combinatorics, Probability and Computing*, Oberwolfach Report 48/2006, Oberwolfach Reports 3 (2006), 2928-2930, Problem 5 (p. 2929), DOI 10.4171/OWR/2006/48.
- Peter Keevash, Fiachra Knox and Richard Mycroft, "Polynomial-time perfect matchings in dense hypergraphs", Advances in Mathematics 269 (2015), 265-334, arXiv:1307.2608 (main theorem: minimum codegree at least $n/k + \gamma n$).
- Jie Han, "Decision problem for perfect matchings in dense $k$-uniform hypergraphs", Transactions of the American Mathematical Society 369 (2017), 5197-5218, arXiv:1409.5931, https://arxiv.org/abs/1409.5931 (main theorem: minimum codegree at least $n/k$).
