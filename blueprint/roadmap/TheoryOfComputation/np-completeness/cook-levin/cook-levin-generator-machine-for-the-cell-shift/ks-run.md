# Correctness of the shift generator on the stack chain of a situation

Let $t < T$,
assume the well-formedness conditions for $N$ situations and stack height $H$, let $i < N$,
and let $F$ be counter values satisfying the block-start conditions at time $t$. Then for
every $n \le K$, where $K$ is the number of stacks, every output $o$ and every Boolean state
$v$, there is a Boolean state $v'$ such that the generator, started at the entry label of the
stacks $< n$ of situation $i$ with state $v$, counters $F$ and output $o$, reaches in at most
$n \cdot B$ steps the entry label of the situation chain for $i$, with state $v'$, counters $F$
and output $e_0 e_1 \cdots e_{n-1}$ followed by $o$. Here $e_k$ is the encoding of the clause
block of situation $i$, stack $k$ at time $t$, and $B$ is the step budget for one block with
$V = (T + 1) W$ variables, $W$ being the number of variables per time step.
