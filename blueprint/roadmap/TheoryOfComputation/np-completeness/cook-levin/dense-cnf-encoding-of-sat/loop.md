# Generic copy loop of the dense-SAT verifier

For a work stack $s$, a partial map $g$ on
the work alphabet $G$, an optional target work stack $t$, and labels $\ell$ (the loop's own
label) and $\ell'$ (its exit), the generic loop is the program statement that does the following.
It pops the top of $s$ and stores the popped symbol $x$ as the machine state (nothing if $s$ is
empty). If $x$ exists and $g(x) = y$ is defined, it pushes $y$ onto $t$ (or pushes nothing when
there is no target stack) and jumps to $\ell$. Otherwise, when $s$ was empty or $g$ is undefined
at $x$, it jumps to $\ell'$.
