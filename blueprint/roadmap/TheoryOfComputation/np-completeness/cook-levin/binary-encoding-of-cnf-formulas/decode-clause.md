# Decoding a length-prefixed clause

Given a bit string $w$, writing $1$ for true and $0$
for false, the decoder reads a unary length prefix $1^n 0$ ($n$ ones followed by a zero) from the
front of $w$, then reads exactly $n$ literals from the remaining bits with the literal decoder.
The result is the clause made of these literals, in order, together with the bits left after
them. Decoding fails if $w$ does not begin with such a prefix or one of the literals cannot be
read.
