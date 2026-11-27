# Decoding a length-prefixed CNF formula

Given a bit string $w$, writing $1$ for true and
$0$ for false, the decoder reads a unary length prefix $1^n 0$ ($n$ ones followed by a zero) from
the front of $w$, then reads exactly $n$ clauses from the remaining bits with the length-prefixed
clause decoder. The result is the CNF formula made of these clauses, in order, together with the
bits left after them. Decoding fails if $w$ does not begin with such a prefix or one of the
clauses cannot be read.
