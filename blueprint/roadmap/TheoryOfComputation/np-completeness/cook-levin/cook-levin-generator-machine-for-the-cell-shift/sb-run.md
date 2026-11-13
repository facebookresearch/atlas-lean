# The decrement chain takes $n$ steps

Fix a layout with $K$ stacks and window depth $d$,
the generator's remaining parameters with $N$ situations, a situation $i < N$ and a stack $k < K$.
For every $n \le d + 1$, every counter valuation $F$ and every $h$ with $F(U) = h + n$, every flag
$v$ and every output $o$, there is a flag $v'$ such that the generator, started at the
decrement-chain label for $n$ remaining decrements of block $(i, k)$ with flag $v$, counters $F$
and output $o$, reaches in exactly $n$ steps the pushed-fill setup label of block $(i, k)$ with
flag $v'$, the counters $F$ with $U$ set to $h$, and the same output $o$.
