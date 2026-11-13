# Step count of the dense CNF-SAT verifier

For bit lists $w$ (a formula) and $y$ (an
assignment), the number $(|w| + 1) + (|y| + 1) + (|w| + 1) + (|y| + 1) + T + 1$, where $T$ is
the step count of the main scan on $w$ started with all of $y$ unused, no assignment bits used
and the clause flag false.

This is the exact number of steps of the verifier machine on input $w \# y$: four passes that
stash and restore $w$ and $y$, the main scan, and one output step.
