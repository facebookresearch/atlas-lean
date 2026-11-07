# A single-tape machine decides the halting problem of a linear bounded automaton

Let $M$
be a linear bounded automaton over a finite tape alphabet $\Sigma$, let $\iota$ be any map from
the Booleans to $\Sigma$, and let $\alpha$ be a primitively encodable type. For $a \in \alpha$, let
$w_a$ be the word obtained by writing, letter by letter through $\iota$, the binary expansion
(least significant bit first) of the natural-number code of $a$. Then the predicate on $\alpha$
that holds at $a$ exactly when $M$ halts on the input $w_a$ is decidable by a single-tape
machine.
