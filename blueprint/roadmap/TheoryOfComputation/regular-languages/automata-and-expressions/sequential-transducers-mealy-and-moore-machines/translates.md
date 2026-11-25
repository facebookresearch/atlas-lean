# Translation by a sequential transducer

A sequential transducer $S$ translates an input
word $x$ to an output word $y$ when the run of $S$ on $x$ from its start state ends in an
accepting state $q$ and $y$ is the concatenation of the initial output of $S$, the output words
emitted by the transitions along the run, and the final output of $S$ at $q$.
