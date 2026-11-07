# A RAM step is sticky at halting states

If the program counter of a state $s$ is at
least the length of a program $P$, then one step of $P$ leaves $s$ unchanged.

A halt instruction sets the program counter to the length of the program, so once a halt has
been executed the state no longer changes.

## Sources

- Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2.
