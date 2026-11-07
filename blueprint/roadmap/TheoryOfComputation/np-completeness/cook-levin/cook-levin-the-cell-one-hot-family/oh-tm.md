# The one-hot generator as a finite multi-stack machine

The one-hot generator for a layout,
bundled as a Mathlib multi-stack Turing machine with finitely many stacks, labels and internal
states: its stacks are the output bit stack and one unary counter for each counter of the
generator, its input stack is the time counter and its output stack is the output stack, it
starts at its first precomputation label with internal state false, and it runs the generator's
program.

This bundling only checks the finiteness conditions; the generator also reads the height bound
from the height counter, which a bundled machine with a single input stack does not record.
