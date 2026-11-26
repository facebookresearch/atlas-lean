# The coded step

For a coded configuration $(l, v, S)$, consisting of an optional label $l$,
an internal state $v$ and coded stacks $S$, the coded step is undefined when $l$ is absent (the
configuration has halted). When $l$ is a label, it is the coded configuration obtained by the coded
execution of the program statement of $l$ from the internal state $v$ on the coded stacks $S$.
