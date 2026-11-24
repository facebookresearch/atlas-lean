# Codes for single-tape machines

A code is a transition table: a finite list of rows, row
$q$ belonging to the state $q \in \mathbb{N}$, each a finite list of entries, entry $a$ of a row
belonging to the symbol $a \in \mathbb{N}$. The entry in row $q$ and column $a$ is either empty,
meaning that the machine halts, or a pair $(q', s)$ of natural numbers, meaning that the machine
enters the state $q'$ and does the action coded by $s$: $0$ moves left, $1$ moves right and
$b + 2$ writes $b$. A state or symbol outside the table halts the machine.
