# Counter-machine instructions

A counter-machine instruction is one of: increment register
$r$, decrement register $r$, or jump to instruction $q$ if register $r$ is zero, where the
register index $r$ and the jump target $q$ are natural numbers.

Decrementing a register that holds $0$ leaves it at $0$.

## Sources

- Minsky, *Computation: Finite and Infinite Machines*, 1967, §11.
