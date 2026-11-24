# A one-state machine that stays in its state on a blank never halts

Let $M$ be a Busy Beaver
machine with a single working state $0$. If the transition of $M$ from state $0$ on reading the
blank symbol $0$ has next state $0$, then $M$ does not halt.

Such a machine marches in one direction forever: at every step the head is on a previously
unvisited blank cell.
