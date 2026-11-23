# Computations extend by unread input and stack bottom

Let $M$ be a pushdown automaton.
If $M$ can compute from a configuration with state $q$, remaining input $w$ and stack $s$ to a
configuration with state $q'$, remaining input $w'$ and stack $s'$, then for every word $v$ and
every list $t$ of stack symbols, $M$ can compute from the configuration with state $q$,
remaining input $wv$ and stack $st$ to the configuration with state $q'$, remaining input $w'v$
and stack $s't$. Here $st$ is the stack $s$ with $t$ placed below it.
