# Correctness of the one-hot generator, with its explicit time bound

Fix a layout, natural
numbers $T$ and $H$, and a bit string $o$. Start the one-hot generator at its first
precomputation label, with internal state false, the output stack holding $o$, the time counter
holding $T$ and the height counter holding $H$ in unary, and every other counter empty. Then
within $\beta(T, H)$ steps, where $\beta$ is the generator's explicit step bound, it reaches its
halting label, in some internal state, with the output stack holding the encoding of the one-hot
cell family for $T$ and $H$ followed by $o$.
