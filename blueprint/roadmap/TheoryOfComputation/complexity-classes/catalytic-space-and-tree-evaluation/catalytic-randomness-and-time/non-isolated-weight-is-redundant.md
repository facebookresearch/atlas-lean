# Agarwala–Mertz: a non-isolated weight is redundant and can be erased from the catalytic tape

Let $W$ be a weight assignment on a bipartite graph and suppose $M_1$ and $M_2$ are both minimum-weight matchings of size $k+1$ with $e\notin M_1$ and $e\in M_2$. Then

$$
w(e)=W(M_1)-W(M_2\setminus\{e\}).
$$

Hence, whenever the matching procedure finds that $W$ fails to isolate size $k+1$, the $\Theta(\log n)$ catalytic bits storing $w(e)$ can be zeroed and later recomputed from $W$ restricted to $E\setminus\{e\}$; this is a compression of the catalytic tape in the compress-or-random paradigm.

## Proof sketch

Both matchings have the same minimum weight, so $W(M_1)=W(M_2)=W(M_2\setminus\{e\})+w(e)$. The matchings $M_1$ and $M_2\setminus\{e\}$ do not involve $w(e)$, and they are recomputable from the remaining weights by rerunning the same deterministic procedure, which makes the erasure reversible.

## Depends on

- [Agarwala–Mertz: isolating weights on the catalytic tape let CLP extend a maximum matching one edge at a time](isolating-weights-extend-matching-in-clp.md)

## Sources

- Aryan Agarwala and Ian Mertz, "Bipartite Matching is in Catalytic Logspace", arXiv:2504.09991 (2025), ECCC TR25-048.
