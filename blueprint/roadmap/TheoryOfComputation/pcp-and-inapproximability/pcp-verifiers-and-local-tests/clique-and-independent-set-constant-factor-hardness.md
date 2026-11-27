# Independent Set and Clique are NP-hard to approximate within every constant factor

For every fixed real $0 < s < 1$, the promise problems $\mathrm{GapIS}_s$ and $\mathrm{GapClique}_s$ are NP-hard under polynomial-time many-one reductions: given a graph $H$ and an integer $k$, yes-instances have an independent set (respectively a clique) of size at least $k$, and no-instances have none of size greater than $s k$. Consequently, unless $\mathrm{P} = \mathrm{NP}$, no polynomial-time algorithm approximates the maximum independent set or maximum clique within any constant factor.

## Proof sketch

By the PCP theorem every NP language has a verifier with $O(\log n)$ randomness, $O(1)$ queries, perfect completeness and soundness $1/2$; repeating it $k$ times independently makes soundness $2^{-k} \le s$ while keeping polynomial size. The FGLSS graph of the repeated verifier has independence number $2^{r}$ on yes-instances and at most $s\, 2^{r}$ on no-instances; complementing the graph gives Clique.

## Depends on

- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [NP-complete decision problems](../../complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [The PCP theorem: NP = PCP(O(log n), O(1))](../pcp-theorem.md)
- [Independence number of the FGLSS graph equals the best acceptance count](fglss-independence-number-equals-acceptance-count.md)
- [Independent repetition multiplies acceptance probabilities](independent-repetition-of-local-tests.md)

## Sources

- U. Feige, S. Goldwasser, L. Lovász, S. Safra and M. Szegedy, "Interactive Proofs and the Hardness of Approximating Cliques", Journal of the ACM 43(2), 1996.
- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
