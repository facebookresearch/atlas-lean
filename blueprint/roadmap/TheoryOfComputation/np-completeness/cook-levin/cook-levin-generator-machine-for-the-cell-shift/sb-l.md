# Label of the decrement chain

Among the generator labels for $N$ situations, $K$ stacks,
$g$ symbol codes and window depth $d$, take a situation $i < N$, a stack $k < K$ and
$n \in \mathbb{N}$. The label is the pushed-fill setup label of block $(i, k)$ if $n = 0$, the
decrement label of block $(i, k)$ with index $n - 1$ if $1 \le n \le d + 1$, and the terminal
label otherwise. It marks the point where $n$ decrements of the counter $U$ remain before the
pushed-fill setup.
