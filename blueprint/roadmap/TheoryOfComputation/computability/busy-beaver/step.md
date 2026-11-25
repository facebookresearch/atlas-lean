# One step of a Busy Beaver machine

Let $M$ be a machine with $n$ working states and let
$c$ be a configuration with head position $h$. If $c$ is halted, the step leaves $c$ unchanged.
Otherwise let $q$ be the current state, let $a$ be the symbol in cell $h$, and let
$M(q, a) = (b, d, q')$. The step writes $b$ in cell $h$, leaving every other cell unchanged, moves
the head to $h - 1$ if $d$ is left and to $h + 1$ if $d$ is right, and passes to the state $q'$,
which may be the halt state.
