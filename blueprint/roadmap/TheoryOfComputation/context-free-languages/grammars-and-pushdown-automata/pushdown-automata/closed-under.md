# Closed sets of stack symbols

A finite set $\Gamma_0$ of stack symbols is closed for a
pushdown automaton $M$ when every transition of $M$ that pops a symbol in $\Gamma_0$, from any
state and on any input letter or on $\varepsilon$, pushes only symbols in $\Gamma_0$.
Computations starting with a stack inside a closed set keep their stack inside it.
