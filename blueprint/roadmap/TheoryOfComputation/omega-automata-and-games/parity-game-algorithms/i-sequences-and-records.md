# i-sequences and records

Let $\pi = p_1 p_2 \cdots p_t$ be a finite sequence of priorities. An *$i$-sequence* in $\pi$ is a set of exactly $2^i$ indices
$1 \le j_1 < \cdots < j_{2^i} \le t$ such that

- (evenness) $p_{j_k}$ is even for every $k < 2^i$;
- (inner domination) whenever $j_k < l < j_{k+1}$, $p_l \le p_{j_k}$ or $p_l \le p_{j_{k+1}}$;
- (outer domination) $p_l \le p_{j_{2^i}}$ for every $l > j_{2^i}$.

A *record* is a tuple $b_k, b_{k-1}, \dots, b_0$ in which each $b_i$ is a priority or the symbol $-$; $b_i \ne -$ is meant to witness an $i$-sequence
whose last priority is $b_i$, the witnessed sequences appearing in order of decreasing $i$. Reading a priority $p$ updates the record in
two steps:

1. let $i$ be the largest index such that $b_j$ is an even priority for every $j < i$; if $b_i = -$ or $b_i < p$, set $b_i := p$ and $b_j := -$ for
   all $j < i$ (otherwise leave the record unchanged);
2. in the result, let $i$ be the largest index with $b_i \ne -$ and $p > b_i$; if there is one, set $b_i := p$
   and $b_j := -$ for all $j < i$.

These play summaries are those of Calude, Jain, Khoussainov, Li and Stephan, in the presentation of the cited chapter.

## Depends on

- [Parity winning condition of a player](../parity-games/wins.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, arXiv:2305.10546v2, 2025, Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Section 2.4, "i-sequences" (the definition with evenness, inner and outer domination), "A data structure for recognising i-sequences" (records, with the witnessing and order properties) and "The update rule" (Steps 1 and 2 and the worked example of Figures 2.3 and 2.4).
