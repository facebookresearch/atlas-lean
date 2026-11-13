# Single-tape simulation of a Post–Turing machine

Let $\Gamma_0$ be a finite alphabet with
blank symbol $b$ and at least one non-blank symbol, and let $M$ be a Post–Turing machine over
$\Gamma_0$ with start state $q_0$, supported by the finite set of states $S$ (so $q_0 \in S$, and
from a state in $S$ the machine $M$ only enters states in $S$). The single-tape machine simulating
$M$ has the non-blank symbols of $\Gamma_0$ as tape alphabet, $S$ as set of states and $q_0$ as
start state. In a state $q$, reading a cell $s$ whose cell symbol is $a$, it acts as follows. If
$M$ halts in $q$ on $a$, it writes $s$ back and halts. If $M$ moves the head in direction $d$ and
enters $q'$, it writes $s$ back, moves in direction $d$ and enters $q'$. If $M$ writes $a'$ and
enters $q'$, it writes the blank cell when $a' = b$ and otherwise the cell holding $a'$, does not
move, and enters $q'$.

CSLib machines need a chosen symbol of their alphabet, so an alphabet whose only symbol is the
blank is excluded.
