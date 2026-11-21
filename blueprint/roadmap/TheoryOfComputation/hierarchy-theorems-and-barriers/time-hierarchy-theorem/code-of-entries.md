# The code of a list of entries

Let $E$ be a list of entries $(q, a, q', s)$ of natural
numbers, and let $Q$ and $M$ be the sums, over the entries of $E$ counted with multiplicity, of
$q + 1$ and of $a + 1$ respectively. The code of $E$ has a table with $Q$ rows and $M$
columns, and for $q < Q$ and $a < M$ its position $(q, a)$ holds $(q', s)$ for the first entry
$(q, a, q', s)$ of $E$ with key $(q, a)$, and is empty (halting) if $E$ has no entry with that
key.
