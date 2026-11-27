# Earley chart as a predicate on items

Let $G$ be a context-free grammar with terminals $T$ and $w$ a word over $T$. An Earley item
$(A \to \gamma, k, p, c)$ (a production, a dot position $k$, the input $p$ before the item's origin and the input
$c$ recognized by the first $k$ symbols of $\gamma$) belongs to the Earley chart of $G$ on $w$ if the
corresponding four-place chart relation holds for $A \to \gamma$, $k$, $p$ and $c$.

## Sources

- J. Earley, "An efficient context-free parsing algorithm", *Communications of the ACM* 13 (1970), 94–102.
