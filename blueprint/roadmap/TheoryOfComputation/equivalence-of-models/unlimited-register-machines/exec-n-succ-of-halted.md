# Bounded URM execution is stable once halted

Let $c$ be a list of instruction codes, $s$
a coded state and $t$ a natural number. If after $t$ steps of bounded execution of $c$ from $s$
the program counter is at least the length of $c$, then $t + 1$ steps of bounded execution of $c$
from $s$ give the same coded state as $t$ steps.
