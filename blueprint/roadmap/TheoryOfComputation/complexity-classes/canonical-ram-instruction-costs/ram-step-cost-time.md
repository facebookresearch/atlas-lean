# The time charged by one RAM step

For a program of length $\ell$ and a state $s$ of the canonical random-access machine, the cost-annotated step charges time $(1, 0, 0)$ if the program counter of $s$ is below $\ell$, so that an instruction is dispatched, and $(0, 0, 0)$ otherwise. It charges for dispatch, not for changes of state, and nothing for steps after halting.
