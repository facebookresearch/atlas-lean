# Reachable pairs of states of two encoded DFAs

For encoded DFAs $D$ and $E$ over the same
alphabet, code a pair $(s, t)$ of natural numbers by its image $\langle s, t \rangle \in \mathbb{N}$
under Mathlib's pairing function. The reachable pairs of $D$ and $E$ form the list returned by the
bounded reachability search on lists of states started at $\langle s_D, s_E \rangle$, where $s_D$
and $s_E$ are the start states of $D$ and $E$, kept inside the list of coded pairs of states of
$D$ and $E$, and in which the successors of a number $p = \langle s, t \rangle$ are the numbers
$\langle s', t' \rangle$ with $s'$ and $t'$ the states that the transition functions of $D$ and
$E$ take $s$ and $t$ to on the same letter $a$, for $a$ running over the letters of $D$ followed
by the letters of $E$.

A number lies in this list exactly when it is $\langle q, r \rangle$ for the states $q$ and $r$
that $D$ and $E$ reach on some common word.
