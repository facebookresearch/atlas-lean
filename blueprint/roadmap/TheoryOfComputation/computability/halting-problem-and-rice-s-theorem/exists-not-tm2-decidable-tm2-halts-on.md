# Some multi-stack machine has an undecidable halting set

There is a multi-stack machine
$M$, with a bijection between its input alphabet and the Booleans, such that no multi-stack
machine decides, for $n \in \mathbb{N}$, whether $M$ halts when started on the binary
representation of $n$ (written in $M$'s input alphabet through the bijection).

The halting set of a code interpreter on input $0$ is r.e., hence the halting set of a
multi-stack machine, and deciding it would decide the halting problem.
