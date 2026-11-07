# Language of a generalized Büchi automaton

An infinite word $x$ belongs to the language of
a generalized Büchi automaton $g$ with acceptance sets $F_0, \dots, F_{k-1}$ iff there is a run
$s$ of $g$ on $x$ such that for every $j < k$ there are infinitely many times $t$ with
$s_t \in F_j$. Here a run of $g$ on $x$ is an infinite sequence of states $s_0, s_1, \dots$ with
$s_0$ a start state and a transition from $s_i$ to $s_{i+1}$ labelled $x_i$ for every $i$.
