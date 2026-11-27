# Machine writing the canonical encoding of a bit list

The multi-stack Turing machine with
the three stacks of the bit-list converters (input, output and a stash), all over bits, reading
its input from the input stack and leaving its output on the output stack, with the two labels
$\mathrm{read}$ and $\mathrm{emit}$ and start label $\mathrm{read}$, an optional bit as internal
state, initially empty, and the program of the bit-list encoder. It moves the input, bit by bit,
onto the stash. Then it pops the stash bit by bit, pushing for each bit $b$ the three bits false,
$b$, true onto the output, so that each block reads true, $b$, false from the top, and halts.
