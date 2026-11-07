# Stack lengths grow by at most the push bound per step

Let $M$ be a finite multi-stack
Turing machine with push bound $B$. If every stack of $S$ has length at most $N$ and $M$ runs in
$n$ steps from a configuration with some label, state $v$ and stacks $S$ to a configuration with
some label, state $v'$ and stacks $S'$, then every stack of $S'$ has length at most $N + Bn$.
