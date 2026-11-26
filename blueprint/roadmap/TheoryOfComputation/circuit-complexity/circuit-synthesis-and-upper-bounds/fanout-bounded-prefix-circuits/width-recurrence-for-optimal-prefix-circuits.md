# Width recurrences for optimal fanout-bounded prefix circuits

For $k\ge2$ and $D\ge1$ let $w_k^\ast(D)$ be the largest $N-1$ such that a zero-deficiency universal prefix circuit with fanout at most $k$ and depth at most $D$ on $N$ inputs exists. Then for $D\ge k$

$$
w_k^\ast(D)=\sum_{i=2}^{k-1}w_k^\ast(D-i)+2\,w_k^\ast(D-k)+k,
$$

and for every $1\le N\le 1+w_k^\ast(D-1)$ an optimal fanout-$k$ prefix circuit of depth at most $D$ on $N$ inputs can be constructed explicitly. The recurrence is derived from an exact recurrence for the widths $w_k(d,h)$ of consistent pairs consisting of a binary interval aggregation tree of depth at most $d$ and a fanout-$k$ prefix distribution tree of depth at most $h$.

## Proof sketch

Decompose an optimal circuit along its principal chain into segments; each segment is a consistent pair of an aggregation tree and a distribution tree, whose maximal widths satisfy a two-parameter recurrence. Optimizing over the segment structure yields the order-$k$ linear recurrence, and the decomposition is reversible, giving the construction.

## Depends on

- [Universal prefix circuits and fanout-bounded optimality](universal-prefix-circuits.md)

## Proof depends on

- [Snir's size–depth trade-off for prefix circuits](snir-size-depth-tradeoff-for-prefix-circuits.md)

## Sources

- Igor S. Sergeev, "A Note on the Depth of Optimal Fanout-Bounded Prefix Circuits", 2025.
