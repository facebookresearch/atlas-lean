# The constant-false code decides the empty language

Let $c$ be the code whose table has
one row, for state $0$: on the input symbols $1$ and $2$ it moves right and stays in state $0$,
and on the blank $0$ it writes $1$, the symbol of the bit $\mathrm{false}$, and enters state
$1$, which has no row, so that $c$ halts. Then $c$ decides the empty language within $n + 1$
steps on every input of length $n$.
