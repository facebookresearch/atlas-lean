# Label after a clause of the cell-shift generator

For a situation $i < N$ and a stack
$k < K$, in block $(i, k)$: after the in-range clause for symbol $x$ the generator goes to the
start of the in-range clause for symbol $x - 1$, or to the in-range drains when $x = 0$; after
the overflow clause it goes to the overflow drains; after the pushed-fill clause for depth $j$
it goes to the start of the pushed-fill clause for depth $j - 1$, or to the pushed-fill drains
when $j = 0$.
