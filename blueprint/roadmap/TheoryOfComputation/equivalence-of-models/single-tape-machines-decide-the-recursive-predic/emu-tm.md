# Finite single-tape emulation of a multi-stack machine

Let $M$ be a multi-stack machine
with finitely many stacks, labels and internal states, and with finite stack alphabets. Its
finite single-tape emulation is the single-tape machine that runs the plain single-tape emulation
of $M$ (through a single-tape machine with a finite store) step for step: its states are those in
the finite set of states the emulation visits, and its tape alphabet is the set of non-blank cells
of the emulation, where a cell is a bottom-of-stack flag together with an optional symbol for each
stack.
