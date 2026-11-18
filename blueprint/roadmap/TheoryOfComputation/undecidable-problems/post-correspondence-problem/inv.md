# Invariant of the rewriting simulation of a single-tape machine

Let $M$ be a single-tape
machine with finitely many tape symbols and states, and $l$ an input. A word $w$ satisfies the
invariant for $l$ when either $w$ spells a configuration that $M$ reaches from its initial
configuration on $l$, or $M$ halts on $l$ and $w = \vdash X\, H\, Y \dashv$ for some words $X$
and $Y$ of tape symbols, where $\vdash$ and $\dashv$ are the left and right end markers and $H$
is the halting symbol. It serves as the invariant of the words reachable from the start word
of $l$.
