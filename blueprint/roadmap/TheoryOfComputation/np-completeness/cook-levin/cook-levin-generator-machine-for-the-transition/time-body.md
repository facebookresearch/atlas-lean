# One iteration of the time loop

Let $t < T$, suppose the tables are well formed at height
$H$ for every situation $i < N$, and let $f$ be a counter assignment that satisfies the time-loop
invariant for $T$ and $H$ and has counter $T_n$ equal to $t$. Then for every output word $o$, the
generator started at the head label of the time-step multiplication, with state $\mathrm{true}$,
counters $f$ and output $o$, reaches the time-loop head label with state $\mathrm{false}$, the same
counters $f$ and output $b_t o$ in at most $B$ steps. Here $b_t$ is the concatenation of the
encoded clauses of time step $t$ for situations $0, \dots, N-1$, and $B$ is the time-loop body
bound for $N$, $T$ and $H$.
