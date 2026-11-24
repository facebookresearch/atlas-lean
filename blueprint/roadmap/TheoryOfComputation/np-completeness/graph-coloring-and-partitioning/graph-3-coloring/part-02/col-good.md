# Well-formed construction states

A construction state $s$ with next free vertex $n$ is
well formed when $3 \le n$; every emitted edge $(a, b)$ has $a < n$, $b < n$ and $a \ne b$; the
literal vertex and the negation vertex of every recorded occurrence are smaller than $n$; the
pairs $(0, 1)$, $(0, 2)$ and $(1, 2)$ are emitted edges (the palette triangle); for every
recorded occurrence with literal vertex $L$ and negation vertex $M$, the pairs $(L, M)$, $(L, 2)$
and $(M, 2)$ are emitted edges; and whenever an occurrence with variable $x$, polarity $b$,
literal vertex $L$ and negation vertex $M$ comes before an occurrence with the same variable $x$,
polarity $b'$, literal vertex $L'$ and negation vertex $M'$ in the list of recorded occurrences
(which lists the latest first), the pairs $(L', M)$ and $(M', L)$ are emitted edges if $b' = b$,
and the pairs $(L', L)$ and $(M', M)$ are emitted edges if $b' \ne b$.
