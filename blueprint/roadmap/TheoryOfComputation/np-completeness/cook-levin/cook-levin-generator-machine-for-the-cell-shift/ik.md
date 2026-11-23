# Entry label of the stack chain of a situation

For natural numbers $i$ and $n$, with $N$
the number of situations and $K$ the number of stacks, this is the entry label of the situation
chain for $i$ when $n = 0$; the first setup stage of block $(i, n - 1)$ when $1 \le n \le K$ and
$i < N$; and the terminal (halting) label otherwise. For $i < N$ and $n \le K$ it is the label
from which the generator emits the blocks of stacks $k < n$ of situation $i$ and then the blocks
of situations $< i$.
