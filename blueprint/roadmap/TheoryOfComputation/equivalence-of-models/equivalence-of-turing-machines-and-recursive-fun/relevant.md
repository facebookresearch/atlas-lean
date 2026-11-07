# Relevant symbols of a stack

For a stack index $k$, the relevant symbols of stack $k$ are
the symbols $f(v)$ of $\Gamma_k$, for every internal state $v$, over all statements that push $f$
onto stack $k$ and occur in the program of some label, together with, when $k$ is the input stack
$k_0$, every symbol of $\Gamma_{k_0}$.

Along a run started from an initial configuration, only relevant symbols occur on the stacks.
