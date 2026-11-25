# The rewriting system simulating a Turing machine

Let $M$ be a single-tape Turing
machine with finitely many states and tape symbols, and write $H$ for the halting symbol. The
rewriting system simulating $M$ is the finite list of rules consisting of the rules for every
state $q$ reading every tape symbol $a$, followed by the erasing rules $c\,H \to H$ and
$H\,c \to H$ for every tape symbol $c$.
