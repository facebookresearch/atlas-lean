# Correctness of the shift generator on the situation chain

Let $t < T$, assume the
well-formedness conditions for $N$ situations and stack height $H$, and let $F$ be counter
values satisfying the block-start conditions at time $t$. Then for every $n \le N$, every
output $o$ and every Boolean state $v$, there is a Boolean state $v'$ such that the generator,
started at the entry label of the situation chain for $n$ with state $v$, counters $F$ and
output $o$, reaches in at most $n \cdot (K \cdot B)$ steps the end-of-time-step label with
state $v'$, counters $F$ and output $e_0 e_1 \cdots e_{n-1}$ followed by $o$. Here $K$ is the
number of stacks, $e_i$ is the concatenated encoding of the clause blocks of situation $i$ for
the stacks $0, \dots, K - 1$ at time $t$, and $B$ is the step budget for one block with
$V = (T + 1) W$ variables, $W$ being the number of variables per time step.
