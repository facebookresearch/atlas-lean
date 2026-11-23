# Two-state Büchi automaton for “eventually always”

For a set $p$ of symbols, this is the
nondeterministic Büchi automaton over the alphabet of symbols with states $\mathsf{false}$ and
$\mathsf{true}$, single start state $\mathsf{false}$ and single accepting state $\mathsf{true}$.
From $\mathsf{false}$ it may read any letter and move to either state; from $\mathsf{true}$ it
may read only letters in $p$, and then it stays in $\mathsf{true}$.
