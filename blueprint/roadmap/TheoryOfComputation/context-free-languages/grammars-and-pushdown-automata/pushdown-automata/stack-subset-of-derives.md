# Computations stay inside a closed set of stack symbols

Let $M$ be a pushdown
automaton and $\Gamma_0$ a finite set of stack symbols that is closed for $M$. If a
configuration $c$ derives a configuration $c'$ in zero or more steps of $M$, and every
symbol on the stack of $c$ lies in $\Gamma_0$, then every symbol on the stack of $c'$ lies
in $\Gamma_0$.
