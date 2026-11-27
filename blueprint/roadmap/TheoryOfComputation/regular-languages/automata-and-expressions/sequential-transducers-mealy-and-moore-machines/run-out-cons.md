# Output of a sequential transducer on a nonempty word

Let $S$ be a sequential
transducer, $q$ a state, $a$ an input letter and $x$ an input word, and let $q'$ and $w$ be the
successor state and the output word of $S$ in state $q$ on letter $a$. The output word of the
run of $S$ from $q$ on $ax$ is $w$ followed by the output word of the run from $q'$ on $x$.
