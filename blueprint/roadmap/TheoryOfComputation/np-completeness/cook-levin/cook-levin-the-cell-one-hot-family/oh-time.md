# Polynomial time bound for the one-hot generator

Fix a layout with label/state block size
$A$, $K$ stacks and $g$ symbol codes, natural numbers $T$ and $H$, and a bit string $o$, and let
$c = 668\,(A + K + g + 1)^7$. Start the one-hot generator at its first precomputation label, with
internal state false, the output stack holding $o$, the time counter holding $T$ and the height
counter holding $H$ in unary, and every other counter empty. Then within $c\,(T + H + 1)^6$
steps it reaches its halting label, in some internal state, with the output stack holding the
encoding of the one-hot cell family for $T$ and $H$ followed by $o$.
