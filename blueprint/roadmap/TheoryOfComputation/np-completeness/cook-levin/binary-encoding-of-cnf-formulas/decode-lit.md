# Decoding a literal

Given a bit string $w$, the decoder reads a prefix-coded natural
number $n$ from the front of $w$ and then one more bit $b$. The result is the literal $(n, b)$,
with variable index $n$ and polarity $b$, together with the bits left after $b$. Decoding fails if
no prefix-coded natural number can be read or no bit follows it.
