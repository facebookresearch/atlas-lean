# Output of a Mealy machine on a nonempty word

Let $M$ be a Mealy machine, $q$ a state,
$a$ an input letter and $x$ an input word, and let $q'$ and $o$ be the successor state and the
output letter of $M$ in state $q$ on letter $a$. The output word of the run of $M$ from $q$ on
$ax$ is $o$ followed by the output word of the run from $q'$ on $x$.
