# Machine decoding the canonical encoding of a bit list

The multi-stack Turing machine with
the three stacks of the bit-list converters (input, output and a stash), all over bits, reading
its input from the input stack and leaving its output on the output stack, with the two labels
$\mathrm{read}$ and $\mathrm{emit}$ and start label $\mathrm{read}$, an optional bit as internal
state, initially empty, and the program of the bit-list decoder. It repeatedly pops an input
symbol; while that symbol is true, it pops two more and pushes the first of them onto the stash
(false if the input ran out before it). Then it moves the stash, bit by bit, onto the output, and
halts.
