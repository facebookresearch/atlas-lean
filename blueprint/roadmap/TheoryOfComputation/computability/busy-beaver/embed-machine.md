# Embedding a machine into one more state

An $n$-state machine $M$ is embedded
into $n + 1$ states as follows. In a working state $q < n$ reading a symbol $s$, the new
machine writes the symbol, makes the move and enters the next state that $M$ prescribes
in state $q$ on $s$, halting when $M$ halts. In the new state $n$ it writes $0$, moves
left and halts, whatever it reads.

No transition enters state $n$. So for $n \ge 1$, where the machine starts in state
$0 < n$, the new state is never reached; for $n = 0$ the new state is the start state.
