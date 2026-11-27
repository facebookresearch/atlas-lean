# One step of a linear bounded automaton

Let $M$ be a linear bounded automaton with state set $Q$ and tape alphabet $\Gamma$. Let $c$ be a configuration with state $q$, tape $x_0 \cdots x_{n-1}$ and head position $h$, and let
$x$ be $x_h$ if $h < n$ and the blank otherwise. A configuration $c'$ is obtained from $c$ by one step of
$M$ if there is a triple $(q', x', d) \in \delta(q, x, \beta(h, n))$, where $\delta$ is the transition
function of $M$ and $\beta(h, n)$ the boundary tag of position $h$ on a tape of length $n$, such that the
move $d$ is legal from $h$ on a tape of length $n$ and $c'$ has state $q'$, the tape obtained from $c$'s
tape by writing $x'$ at position $h$, and head position $h - 1$, $h$ or $h + 1$ according as $d$ is left,
stay or right.

Legality requires $h < n$ for every move, so no step starts from a configuration whose head is off the
tape, and no step moves the head off the tape.
