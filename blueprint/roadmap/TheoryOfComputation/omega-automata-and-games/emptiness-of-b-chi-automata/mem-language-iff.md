# Büchi acceptance condition

A nondeterministic Büchi automaton accepts an infinite word
$x = x_0 x_1 x_2 \cdots$ if and only if it has a run on $x$, that is, a sequence of states
$s_0 s_1 s_2 \cdots$ with $s_0$ a start state and a transition from $s_k$ to $s_{k+1}$ reading
$x_k$ for every $k$, such that $s_k$ is an accepting state for infinitely many $k$.
