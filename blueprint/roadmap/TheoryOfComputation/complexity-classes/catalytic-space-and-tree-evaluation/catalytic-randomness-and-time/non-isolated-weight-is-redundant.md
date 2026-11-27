# Agarwala–Mertz: a non-isolated weight is redundant and can be erased from the catalytic tape

Let $W$ be a weight assignment on a bipartite graph and suppose $M_1$ and $M_2$ are both minimum-weight matchings of size $k+1$ with $e\notin M_1$ and $e\in M_2$. Then

$$
w(e)=W(M_1)-W(M_2\setminus\{e\}).
$$

Hence such a weight is redundant once the rest of the configuration is known, which is a compression of the catalytic tape in the compress-or-random paradigm. In the source it is used as follows. Suppose the weights $W$, stored on the catalytic tape with $5\log n$ bits each, isolate a minimum-weight matching $M^k$ of size $k$ but not of size $k+1$, and $5\log n$ further catalytic bits hold a reserve weight $r$. A $\mathsf{CLP}$ subroutine finds an edge $e = u \to v$ of the residual graph of $M^k$, with $e \notin M^k$, that lies on some but not all minimum-weight source-sink paths; it replaces $w(e)$ by $r$ and overwrites the reserve with $k$ and the endpoints $u, v$ of $e$, which take $\log n$ bits each, so $2\log n$ catalytic bits are freed. Recovery of $w(e)$ needs $k$ and $e$ besides the remaining weights: it works from $(G \setminus \{e\}, k, W|_{E\setminus\{e\}})$.

## Proof sketch

Both matchings have the same minimum weight, so $W(M_1)=W(M_2)=W(M_2\setminus\{e\})+w(e)$. For the recovery, since $e \notin M^k$, the matching $M^k$ is still the isolated minimum-weight matching of size $k$ in $G \setminus \{e\}$, so it and its residual graph can be recomputed without $w(e)$. In the residual graph, whose cycles all have positive weight, write $\delta_{a,b}$ for the minimum weight of an $a$-$b$ path and $\delta'_{s,t}$ for the minimum weight of a source-sink path avoiding $e$. Since $e$ lies on some but not all minimum-weight source-sink paths, $\delta_{s,u} + w(e) + \delta_{v,t} = \delta_{s,t} = \delta'_{s,t}$, so $w(e) = \delta'_{s,t} - (\delta_{s,u} + \delta_{v,t})$, and none of these three quantities involves $w(e)$. Undoing the replacement then restores the catalytic tape.

## Depends on

- [Agarwala–Mertz: isolating weights on the catalytic tape let CLP extend a maximum matching one edge at a time](isolating-weights-extend-matching-in-clp.md)

## Sources

- Aryan Agarwala and Ian Mertz, "Bipartite Matching is in Catalytic Logspace", FOCS (2025); arXiv:2504.09991, ECCC TR25-048 (Lemmas 5.4 and 5.5).
