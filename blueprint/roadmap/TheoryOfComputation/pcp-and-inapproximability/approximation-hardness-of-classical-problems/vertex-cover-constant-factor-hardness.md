# Vertex Cover is NP-hard to approximate within some constant factor

There is a constant $\rho > 1$ such that, unless $\mathrm{P} = \mathrm{NP}$, no polynomial-time algorithm computes a vertex cover of size at most $\rho$ times the minimum. Equivalently, a gap version of Vertex Cover, with vertex covers of size at most $k$ versus all covers larger than $\rho k$, is NP-hard; it follows from the gap hardness of Independent Set in graphs whose maximum independent set has a constant fraction of the vertices, since complements of independent sets are vertex covers.

## Proof sketch

In the FGLSS graph of a constant-query PCP verifier with $2^r$ random strings, each random string contributes a clique of views; yes-instances have independent sets of size $2^r$ and no-instances at most $2^{r-1}$. With $V$ the number of views (at most $c\, 2^r$ for a constant $c$), minimum vertex covers have size $V - 2^r$ versus at least $V - 2^{r-1}$, a constant ratio.

## Depends on

- [NP-complete decision problems](../../complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [Independence number of the FGLSS graph equals the best acceptance count](../pcp-verifiers-and-local-tests/fglss-independence-number-equals-acceptance-count.md)
- [The PCP theorem: NP = PCP(O(log n), O(1))](../pcp-theorem.md)

## Sources

- U. Feige, S. Goldwasser, L. Lovász, S. Safra and M. Szegedy, "Interactive Proofs and the Hardness of Approximating Cliques", Journal of the ACM 43(2), 1996.
- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
