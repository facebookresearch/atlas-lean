# Acceptance by the Earley recognizer

Let $G$ be a context-free grammar with terminals $T$ and initial nonterminal $S$. The Earley recognizer
of $G$ accepts a word $w$ over $T$ when the Earley chart of $G$ on $w$ contains a completed item for a
production of $S$ that started at the beginning of $w$ and consumed all of $w$: an item $E(r, k, p, c)$
with left side of $r$ equal to $S$, $k$ the length of the right side of $r$, $p$ empty and $c = w$.

## Sources

- J. Earley, "An efficient context-free parsing algorithm", *Communications of the ACM* 13 (1970), 94–102.
