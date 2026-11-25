# Extending a well-formed state keeps it well formed

Let $s$ be a well-formed
construction state with next free vertex $m$, let $n \ge m$, and let $E$ be a list of pairs
$(a, b)$ of natural numbers with $a < n$, $b < n$ and $a \ne b$. Then the state with next free
vertex $n$, the same recorded occurrences as $s$, and emitted edges those of $s$ followed by $E$
is well formed.
