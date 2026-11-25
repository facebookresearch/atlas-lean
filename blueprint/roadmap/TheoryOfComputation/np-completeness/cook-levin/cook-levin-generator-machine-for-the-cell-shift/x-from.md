# Entry label of the in-range chain

For a situation $i < N$, a stack $k < K$ and a number
$n$, the label of the generator with $N$ situations, $K$ stacks, $g$ symbol codes and window
depth $d$ from which the in-range shift clauses for the symbol codes $x < n$ of the current cell
pair of block $(i, k)$ are emitted before the in-range drains: the in-range drain stage
$\mathrm{dCB}$ of block $(i, k)$ if $n = 0$, the first stage of the routine emitting the in-range
shift clause for symbol code $n - 1$ of block $(i, k)$ if $1 \le n \le g$, and the halting label
$\mathrm{done}$ (unused) if $n > g$.
