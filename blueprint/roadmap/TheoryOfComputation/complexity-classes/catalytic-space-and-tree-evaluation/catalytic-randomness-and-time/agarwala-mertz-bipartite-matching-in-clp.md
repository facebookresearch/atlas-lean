# Agarwala–Mertz: bipartite maximum matching is in polynomial-time catalytic logspace (MATCH ∈ CLP)

Let $\mathrm{MATCH}$ be the function mapping an $n\times n$ bipartite graph to a matching of maximum size. Then $\mathrm{MATCH}\in\mathsf{CLP}\subseteq\mathsf{CL}$. This is the first well-studied subclass of $\mathsf{P}$ known to contain $\mathrm{MATCH}$, the first algorithm for $\mathrm{MATCH}$ using simultaneously polynomial time and sublinear free space with any additional resource, and the first problem shown to be in $\mathsf{CL}$ that is not known to be in $\mathsf{TC}^1$. In particular, any proof that $\mathsf{CL}$ or $\mathsf{CLP}$ lies in $\mathsf{NC}$ would put bipartite matching in $\mathsf{NC}$.

## Proof sketch

Split the catalytic tape into a computation area, a weight assignment $W$ with $\Theta(\log n)$ bits per edge, and polynomially many reserve weights. Starting with $k=1$, certify isolation for successive sizes and compute the isolated matchings; if some size $k+1$ is not isolated, erase the redundant weight found, replace it by a reserve weight, and restart. After polynomially many rounds either the maximum matching is isolated and output, or enough bits have been freed to compute a maximum matching by a direct polynomial-time algorithm; finally the erased weights are restored one by one in reverse order.

## Depends on

- [The class NC](../../time-and-space-complexity-classes/nc.md)
- [Polynomial-time catalytic logspace CLP and zero-error polynomial-time catalytic logspace CZPLP](polynomial-time-catalytic-logspace-classes.md)

## Proof depends on

- [Agarwala–Mertz: a non-isolated weight is redundant and can be erased from the catalytic tape](non-isolated-weight-is-redundant.md)
- [Agarwala–Mertz: isolating weights on the catalytic tape let CLP extend a maximum matching one edge at a time](isolating-weights-extend-matching-in-clp.md)
- [General matching is in P (Edmonds' blossom algorithm)](../../../polynomial-time-problems/matching-in-general-graphs/matching-in-p.md)

## Sources

- Aryan Agarwala and Ian Mertz, "Bipartite Matching is in Catalytic Logspace", arXiv:2504.09991 (2025), ECCC TR25-048.
