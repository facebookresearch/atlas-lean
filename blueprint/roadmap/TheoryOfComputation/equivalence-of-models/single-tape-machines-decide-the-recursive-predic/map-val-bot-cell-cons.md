# The bottom cell followed by the input word is the emulation's start tape

Let $M$ be a
multi-stack machine with finitely many stacks, labels and internal states, and let $e$ be a
bijection from the alphabet of its input stack to the bits. For every list of bits $w$, the bottom
cell followed by the input cells of the bits of $w$, read as cells of the emulation, is the start
tape that the single-tape emulation assigns to the input stack obtained by applying $e^{-1}$ to
each entry of the reversal of $w$ followed by $\mathsf{true}$.
