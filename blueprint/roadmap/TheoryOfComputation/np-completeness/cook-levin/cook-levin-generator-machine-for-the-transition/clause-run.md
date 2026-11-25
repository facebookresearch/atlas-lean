# Run of the transition-family generator on one clause

Let $L$ be a layout with tables
$la$, $na$, $wa$, let $N$ be the number of situations, let $T$, $H$, $t$ be natural numbers with
$t < T$, and let $i < N$ be a situation whose tables are well formed at height $H$. Let $F$ be
counter values at rest in the time loop at time $t$ (for $T$ and $H$) with $F(\mathrm{P}) = 0$,
let $o$ be a bit string and $v$ a Boolean machine state. Started at the first label of the clause
routine for situation $i$ with state $v$, counter values $F$ and output stack $o$, the generator
reaches, in at most $C$ steps, the label after the clause of situation $i$ with state false,
counter values $F$, and output stack the encoding of the dense clause over $V$ variables with the
literals of clause $(t, i)$ followed by $o$. Here $V$ is the number of variables of $L$ for $T$
and $H$, and $C$ is the step bound for one whole clause of $L$ for $T$ and $H$.
