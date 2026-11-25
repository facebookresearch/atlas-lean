# Soundness of the Earley chart

Let $G$ be a context-free grammar with terminals $T$ and $w$ a word over $T$, and consider the Earley chart of $G$ on $w$: its items $E(r, k, p, c)$ consist of a production $r$ of $G$, a dot position $k \in \mathbb{N}$, and words $p$ and $c$ over $T$ (the input before the item started and the input the item has consumed).
For every item $E(r, k, p, c)$ of the chart, the first $k$ symbols of the right side of $r$ yield the
consumed word $c$ in $G$.

## Sources

- J. Earley, "An efficient context-free parsing algorithm", *Communications of the ACM* 13 (1970), 94–102.
