# The online matrix-vector multiplication conjecture

In the *online Boolean matrix-vector multiplication* problem (OMv), an algorithm first receives an integer $n$ and an $n \times n$ Boolean matrix $M$. For $n$ rounds $i = 1, \dots, n$, it then receives a Boolean column vector $v_i$ of length $n$ and must output $M v_i$, computed over the Boolean semiring with $\vee$ as addition and $\wedge$ as multiplication, before it receives $v_{i+1}$. Its running time is the total time for preprocessing and all $n$ rounds, in the [word-RAM model](the-word-ram-model.md).

The naive algorithm takes $O(n^2)$ time per round and $O(n^3)$ in total. Known algorithms improve on this only by subpolynomial factors, for example Williams's $O(n^3 / \log^2 n)$ algorithm.

**OMv conjecture.** For every constant $\varepsilon > 0$, no algorithm solves OMv in time $O(n^{3 - \varepsilon})$ with error probability at most $1/3$.

This is an open hypothesis. It can be argued to follow from the combinatorial Boolean matrix multiplication conjecture when "combinatorial" is read as "not Strassen-like". Under the OMv conjecture, many [dynamic graph problems](dynamic-graph-problems.md) have tight polynomial lower bounds on their update and query times.

## Depends on

- [The word-RAM model](the-word-ram-model.md)

## Background

- [Fine-grained reductions](fine-grained-reductions.md)
- [The 3SUM, APSP and Orthogonal Vectors hypotheses](the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)

## Sources

- M. Henzinger, S. Krinninger, D. Nanongkai and T. Saranurak, "Unifying and strengthening hardness for dynamic problems via the online matrix-vector multiplication conjecture", *Proceedings of the 47th ACM STOC*, 2015, arXiv:1511.06773, <https://arxiv.org/abs/1511.06773>, Section 1: the definition of OMv, the naive $O(n^3)$ algorithm, the $O(n^3/\log n)$ and $O(n^3/\log^2 n)$ algorithms, Conjecture 1.1 (the OMv conjecture), and the relation to the combinatorial BMM conjecture.
