# The singleton machine

A one-stack machine with a single control label and one Boolean of internal state that turns the one-bit encoding of a bit $b$ into the three-bit encoding of the list $[b]$: it pops $b$ (reading false from an empty stack), pushes false, $b$ and true, resets the internal state to false and halts. The same stack holds input and output.
