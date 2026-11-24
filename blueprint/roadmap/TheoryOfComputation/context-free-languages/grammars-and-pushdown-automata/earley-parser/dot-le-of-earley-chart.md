# Earley item dot stays within its production

Let $G$ be a context-free grammar with terminals $T$ and $w$ a word over $T$, and consider the Earley chart of $G$ on $w$: its items $E(r, k, p, c)$ consist of a production $r$ of $G$, a dot position $k \in \mathbb{N}$, and words $p$ and $c$ over $T$ (the input before the item started and the input the item has consumed).
For every item $E(r, k, p, c)$ of the chart, the dot position $k$ is at most the length of the right
side of $r$.

## Sources

- J. Earley, "An efficient context-free parsing algorithm", *Communications of the ACM* 13 (1970), 94–102.
