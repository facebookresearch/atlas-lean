# Bounded URM execution stays at its halted value

Let $c$ be a list of instruction codes,
$s$ a coded state, and $t_1 \le t_2$ natural numbers. If after $t_1$ steps of bounded execution
of $c$ from $s$ the program counter is at least the length of $c$, then $t_2$ steps of bounded
execution of $c$ from $s$ give the same coded state as $t_1$ steps.
