# Program of the bit-list encoder

The program of the machine that writes the canonical
encoding of a bit list acts on the three stacks of the bit-list converters, all over bits, with an
optional bit as internal state. At label $\mathrm{read}$ it pops a bit from the input stack,
pushes it onto the stash and returns to $\mathrm{read}$; when the input is empty it goes to
$\mathrm{emit}$. At label $\mathrm{emit}$ it pops a bit $b$ from the stash, pushes false, $b$ and
true onto the output, so that the output then reads true, $b$, false from the top, and returns to
$\mathrm{emit}$; it halts when the stash is empty.
