# Output of a sequential transducer on a concatenation

For a sequential transducer $S$,
a state $q$ and input words $x$ and $y$, the output word of the run of $S$ from $q$ on $xy$ is
the output word of the run from $q$ on $x$ followed by the output word of the run on $y$ from
the final state of the run from $q$ on $x$.
