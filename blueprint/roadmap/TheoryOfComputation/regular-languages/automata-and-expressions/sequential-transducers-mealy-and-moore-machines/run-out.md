# Output word of a sequential transducer run

For a sequential transducer $S$, a state $q$
and an input word $x$, the output word of the run from $q$ on $x$ is the concatenation of the
output words that $S$ emits on the successive letters of $x$, starting in $q$ and moving to the
successor state after each letter; the initial and final outputs are not included.
