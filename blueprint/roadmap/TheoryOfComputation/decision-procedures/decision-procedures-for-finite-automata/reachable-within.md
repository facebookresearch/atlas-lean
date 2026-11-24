# Early-stopping DFA reachability search

Let $M$ be a DFA over a finite alphabet whose set
of states has decidable equality. For a natural number $n$ and a finite set $S$ of states of $M$,
the reachability search from $S$ with at most $n$ rounds returns $S$ when $n = 0$. When
$n = k + 1$, it returns $S$ if one round of the reachability search for $M$ sends $S$ to $S$
itself, and otherwise it returns the search from the image of $S$ under that round with at most
$k$ rounds.
