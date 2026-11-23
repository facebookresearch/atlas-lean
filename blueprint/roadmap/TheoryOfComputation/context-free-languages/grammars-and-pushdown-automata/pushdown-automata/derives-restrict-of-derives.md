# Computations inside a closed set lift to the restriction

Let $M$ be a pushdown automaton
and let $\Gamma_0$ be a finite set of stack symbols that contains the initial stack symbol of $M$
and is closed for $M$. Suppose $M$ can compute from a configuration with state $q$, remaining
input $w$ and stack $s$ to a configuration with state $q'$, remaining input $w'$ and stack $s'$,
and every symbol of $s$ lies in $\Gamma_0$. Then the symbols of $s'$ also lie in $\Gamma_0$, and
the restriction of $M$ to $\Gamma_0$ can compute from the configuration $(q, w, s)$ to the
configuration $(q', w', s')$, with $s$ and $s'$ read as stacks over $\Gamma_0$.
