# Correctness of the shift generator on one block

Let $t < T$, assume the
well-formedness conditions for $N$ situations and stack height $H$, let $i < N$ and $k < K$,
where $K$ is the number of stacks, and let $F$ be counter values satisfying the block-start
conditions at time $t$. Then for every output $o$ and every Boolean state $v$, the generator,
started at the first setup stage of block $(i, k)$ with state $v$, counters $F$ and output $o$,
reaches in at most $B$ steps the entry label of the stacks $< k$ of situation $i$, with state
false, counters $F$ and output $e$ followed by $o$. Here $e$ is the encoding of the clause block
of situation $i$, stack $k$ at time $t$, and $B$ is the step budget for one block with
$V = (T + 1) W$ variables, $W$ being the number of variables per time step.
