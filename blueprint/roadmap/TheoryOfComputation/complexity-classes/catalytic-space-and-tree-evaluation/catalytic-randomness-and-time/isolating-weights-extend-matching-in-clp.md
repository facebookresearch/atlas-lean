# Agarwala–Mertz: isolating weights on the catalytic tape let CLP extend a maximum matching one edge at a time

Let $G$ be an $n\times n$ bipartite graph and $W:E\to\{0,\dots,\mathrm{poly}(n)\}$ a weight assignment. Say $W$ isolates size $k$ if $G$ has a unique matching $M^k$ of minimum weight among matchings of size $k$. Given $W$ (possibly stored on the catalytic tape) and $k$ such that $W$ isolates size $k$, a $\mathsf{CLP}$ machine can:

1. compute $M^k$, from the lowest nonzero bit of the determinant of an Edmonds-type matrix with entries $2^{w(e)}$, as in Mulmuley–Vazirani–Vazirani;
2. decide which of three cases holds: $G$ has no matching of size $k+1$; $W$ isolates size $k+1$; or there are at least two minimum-weight matchings of size $k+1$, in which case it outputs an edge $e$ lying in some but not all of them, together with minimum-weight matchings $M_1\not\ni e$ and $M_2\ni e$ of size $k+1$.

This uses the residual graph of $G$ with respect to $M^k$ with added source and sink, whose source-sink paths are augmenting paths encoding matchings of size $k+1$ and their weights, and the facts that determinants and minimum-weight directed paths are computable in $\mathsf{CLP}$ (via $\mathsf{TC}^1\subseteq\mathsf{CLP}$ and $\mathsf{NL}\subseteq\mathsf{CLP}$).

## Proof sketch

Under isolation the Mulmuley–Vazirani–Vazirani argument identifies $M^k$ edge by edge from determinant computations, which lie in $\mathsf{TC}^1\subseteq\mathsf{CLP}$. Minimum-weight matchings of size $k+1$ correspond to minimum-weight source-sink paths in the residual graph, which has no negative cycles by minimality of $M^k$; minimum path weights are found in $\mathsf{CLP}$ by binary search over $\mathsf{NL}$ queries, and comparing the optimum with and without each edge detects non-uniqueness and produces $e$, $M_1$, $M_2$.

## Depends on

- [Polynomial-time catalytic logspace CLP and zero-error polynomial-time catalytic logspace CZPLP](polynomial-time-catalytic-logspace-classes.md)

## Proof depends on

- [Isolation lemma](../../../../Combinatorics/probabilistic-combinatorics/isolation-lemma.md)
- [General matching is in P (Edmonds' blossom algorithm)](../../../polynomial-time-problems/matching-in-general-graphs/matching-in-p.md)

## Sources

- Aryan Agarwala and Ian Mertz, "Bipartite Matching is in Catalytic Logspace", arXiv:2504.09991 (2025), ECCC TR25-048.
- Ketan Mulmuley, Umesh V. Vazirani and Vijay V. Vazirani, "Matching is as Easy as Matrix Inversion", Combinatorica 7(1) (1987).
