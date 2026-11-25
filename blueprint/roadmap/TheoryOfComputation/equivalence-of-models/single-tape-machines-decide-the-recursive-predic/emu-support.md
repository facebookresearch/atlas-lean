# States of the single-tape emulation

Let $M$ be a multi-stack machine with finitely many
stacks, labels and internal states and a finite input alphabet. Its plain single-tape emulation
is the translation of $M$ to a single-tape machine with a finite store, followed by the
translation of that machine to a plain single-tape machine, whose states are pairs of a
statement of the intermediate machine, or the halting state, and an internal state. This is the
finite set of those pairs whose first entry is the halting state or a statement occurring in the
program of one of the labels that the first translation produces from the labels of $M$.

The emulation only visits states in this set.
