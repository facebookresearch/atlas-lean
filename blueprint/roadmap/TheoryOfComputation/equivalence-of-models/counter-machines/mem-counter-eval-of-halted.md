# Output membership for counter machines

Let $P$ be a counter-machine program, let $x$ be
a list of natural-number inputs, and let $t$ and $y$ be natural numbers. If the state reached
after $t$ steps of $P$ from the initial state on $x$ has program counter at least the length
of $P$ (so the machine has halted) and register $0$ holds $y$ in that state, then the output
of $P$ on $x$ is defined and equals $y$.

## Sources

- Minsky, *Computation: Finite and Infinite Machines*, 1967, §11.
