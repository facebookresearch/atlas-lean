# One step of a counter machine

Let $p$ be a counter-machine program, a list of
instructions indexed from $0$, and let $s$ be a state with program counter $c$. If $c$ is at
least the length of $p$ (the machine has halted), the step leaves $s$ unchanged. Otherwise it
executes instruction $c$ of $p$: increment register $r$ adds $1$ to register $r$ and sets the
program counter to $c + 1$; decrement register $r$ subtracts $1$ from register $r$ if it is
positive, leaves it at $0$ otherwise, and sets the program counter to $c + 1$; jump to $q$ if
register $r$ is zero leaves the registers unchanged and sets the program counter to $q$ if
register $r$ holds $0$ and to $c + 1$ otherwise.

Because halted states are fixed, the step can be iterated any number of times.

## Sources

- Minsky, *Computation: Finite and Infinite Machines*, 1967, §11.
