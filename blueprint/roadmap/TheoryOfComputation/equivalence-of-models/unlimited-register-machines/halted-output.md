# Output after a given number of steps

For a URM program $p$, an input $x$ and a number
$t$, run bounded execution for $t$ steps on the instruction codes of $p$ from the initial coded
state for $x$. If the resulting program counter is less than the length of the list of
instruction codes, the program is still running and there is no output; otherwise the output
is the entry at position $0$ of the resulting register list, read with default $0$.
