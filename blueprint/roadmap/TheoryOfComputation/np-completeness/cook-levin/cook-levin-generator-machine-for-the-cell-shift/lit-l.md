# Entry label of a literal routine of the cell-shift generator

For a situation $i < N$, a
stack $k < K$, a clause kind $c$ and $l \in \mathbb{N}$, the entry label of literal $l$ is the
first stage of the routine emitting literal $l$ of a clause of kind $c$ in block $(i, k)$ when
$l < 3$, and the generator's final label when $l \ge 3$ (that case is never used).
