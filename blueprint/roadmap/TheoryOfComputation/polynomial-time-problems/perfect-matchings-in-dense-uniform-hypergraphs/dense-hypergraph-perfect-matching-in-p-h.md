# Perfect matchings in dense hypergraphs are decidable in polynomial time

Resolved true: Keevash, Knox and Mycroft give a polynomial-time algorithm when the minimum codegree
is at least `n/k + γn` for a fixed `γ > 0`, and Han extends it to minimum codegree at least `n/k`,
so the problem is in `P` for every `1/k ≤ c < 1/2`. Inputs whose edge count is below what the
codegree condition forces are rejected first, so `n` is polynomial in the input size whenever the
remaining checks run. Source: A. Ruciński, in Combinatorics, Probability and Computing, Oberwolfach
Reports 3 (2006), no. 48, p. 2929, Problem 5, DOI 10.4171/OWR/2006/48; resolution: P. Keevash, F.
Knox and R. Mycroft, Polynomial-time perfect matchings in dense hypergraphs, Adv. Math. 269 (2015),
265-334, arXiv:1307.2608 (c > 1/k); J. Han, Decision problem for perfect matchings in dense
k-uniform hypergraphs, Trans. Amer. Math. Soc. 369 (2017), 5197-5218, arXiv:1409.5931 (c = 1/k), KKM
main theorem (codegree ≥ n/k + γn) and Han main theorem (codegree ≥ n/k): polynomial-time decision,
https://arxiv.org/abs/1409.5931.
