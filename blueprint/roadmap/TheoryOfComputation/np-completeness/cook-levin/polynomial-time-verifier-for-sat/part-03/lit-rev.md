# A literal's tokens on the token stack

For a literal $(n, p)$ with variable index $n$ and
polarity $p$, the list of symbols consisting of the literal marker of polarity $p$ followed by
the bits of the binary encoding of $n$ (least significant bit first, empty for $n = 0$) in
reverse order.
