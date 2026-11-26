# The finite-state machine of a code

For a code $c$ with $k$ work tapes and state bound
$N$, this is the binary machine with $k$ work tapes and states $0, 1, \dots, N - 1$ that starts
in state $0$ and, in a state $q < N$ reading $a$ under the input head and $w$ under the work
heads, takes the action of $c$ at $(q, a, w)$, with a successor state not below $N$ replaced by
halting. Since every state the machine of $c$ can enter is below $N$, it is the machine of $c$
with its states restricted to those below $N$.
