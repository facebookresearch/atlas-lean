# The zero test is a register-machine jump against a zero register

If, at the current program counter of a counter-machine state $s$, the counter program has "if register $r$ is zero, jump to $j$", an unlimited register machine program has "if registers $r$ and $z$ are equal, jump to $j$", and register $z$ holds $0$ in $s$, then one counter-machine step from $s$ corresponds to one step of the register machine program.
