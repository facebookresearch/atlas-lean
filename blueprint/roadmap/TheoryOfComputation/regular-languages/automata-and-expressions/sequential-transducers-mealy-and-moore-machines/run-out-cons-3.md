# Output of a Moore machine on a nonempty word

Let $M$ be a Moore machine, $q$ a state,
$a$ an input letter and $x$ an input word, and let $q'$ be the successor state of $M$ in state
$q$ on letter $a$. The output word of the run of $M$ from $q$ on $ax$ is the output of $q$
followed by the output word of the run from $q'$ on $x$.
