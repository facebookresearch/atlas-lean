# Polarity-first tokens of a literal

For a literal $(x, p)$ with variable index
$x \in \mathbb{N}$ and polarity $p$, the token list is the polarity marker symbol for $p$
followed by one name-bit symbol for each bit of the canonical binary representation of $x$
(least significant bit first, empty for $x = 0$), in order.

This is how the CLIQUE emitter writes a walked literal occurrence on its stack $D$, top first.
