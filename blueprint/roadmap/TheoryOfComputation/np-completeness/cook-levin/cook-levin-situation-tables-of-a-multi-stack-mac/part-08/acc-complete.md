# Completeness of the accept family

Let $E$ be an encoding of the machine $M$, let $s$ be
a word over the input alphabet, let $T$ and $H$ be natural numbers with $H > 0$, and let
$\mathrm{acc}$ be a symbol of the output stack. Suppose that the configuration reached after $T$
steps of the idle-extended run of $M$ from the initial configuration on $s$ is accepting for
$\mathrm{acc}$: it is halted, its state is the initial state of $M$, and $\mathrm{acc}$ is on top
of its output stack. Then the assignment of the real run's literals of $s$ for $T$ steps at
height $H$ satisfies the accept family for $\mathrm{acc}$ at $T$ and $H$, both its positive and
its negated unit clauses.
