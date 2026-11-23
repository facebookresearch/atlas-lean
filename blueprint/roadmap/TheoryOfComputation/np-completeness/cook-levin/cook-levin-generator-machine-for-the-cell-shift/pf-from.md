# Entry label of the pushed-fill chain

For a situation $i < N$, a stack $k < K$ and a
number $n$, the label of the generator with $N$ situations, $K$ stacks, $g$ symbol codes and
window depth $d$ from which the pushed-fill clauses $j < n$ of block $(i, k)$ are emitted before
the fill drains: the fill-drain stage $\mathrm{fD1}$ of block $(i, k)$ if $n = 0$, the first
stage of the routine emitting pushed-fill clause $n - 1$ of block $(i, k)$ if $1 \le n \le d$,
and the halting label $\mathrm{done}$ (unused) if $n > d$.
