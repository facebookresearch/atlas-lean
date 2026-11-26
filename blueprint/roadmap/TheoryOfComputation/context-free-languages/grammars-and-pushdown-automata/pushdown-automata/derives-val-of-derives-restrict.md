# Computations of the restriction are computations of the automaton

Let $M$ be a pushdown
automaton and let $\Gamma_0$ be a finite set of stack symbols that contains the initial stack
symbol of $M$ and is closed for $M$. If the restriction of $M$ to $\Gamma_0$ can compute from a
configuration with state $q$, remaining input $w$ and stack $s$ to a configuration with state
$q'$, remaining input $w'$ and stack $s'$, then $M$ can compute from the configuration
$(q, w, s)$ to the configuration $(q', w', s')$, where the stacks $s$ and $s'$ over $\Gamma_0$ are
read as stacks over the full stack alphabet of $M$.
