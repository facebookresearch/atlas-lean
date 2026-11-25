# Finitely supported pushdown automata

A pushdown automaton $M$ is finitely supported when
there are finite sets $\sigma_0$ of states, $\Gamma_0$ of stack symbols and $T_0$ of input letters
such that the start state lies in $\sigma_0$, the initial stack symbol lies in $\Gamma_0$, every
transition from a state in $\sigma_0$ that pops a symbol in $\Gamma_0$ (on any input letter or on
$\varepsilon$) moves to a state in $\sigma_0$ and pushes only symbols in $\Gamma_0$, and there is
no transition from a state in $\sigma_0$ popping a symbol in $\Gamma_0$ that consumes an input
letter outside $T_0$.

This is the finiteness condition of a standard pushdown automaton; computations from the initial
configuration then only ever visit finitely many states, push finitely many stack symbols, and
respond to finitely many input letters.
