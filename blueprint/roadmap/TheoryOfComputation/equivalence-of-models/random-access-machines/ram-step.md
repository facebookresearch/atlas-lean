# One step of a RAM machine

Let $P = (P_0, \dots, P_{\ell-1})$ be a program of length
$\ell$ and $s$ a state with program counter $p$, accumulator $a$ and register contents $r$. If
$p \ge \ell$, the step leaves $s$ unchanged. Otherwise it executes $P_p$, where $v$ denotes
the value of the instruction's operand in $s$: a load sets the accumulator to $v$, an add sets
it to $a + v$, a subtract sets it to $\max(a - v, 0)$, and a store writes $a$ into the
register that its destination resolves to in $s$; each of these also increases the program
counter by $1$. A jump to $q$ sets the program counter to $q$; a jump-if-zero to $q$ sets it
to $q$ if $a = 0$ and to $p + 1$ otherwise; a halt sets it to $\ell$. Nothing else changes.

In particular, once the program counter is at least $\ell$ (for instance after a halt), every
further step leaves the state unchanged.

## Sources

- Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2.
