# A clause's tokens on the token stack

For a clause with literals $l_1, \dots, l_k$, the
list of symbols consisting of the clause marker followed by the stack tokens of $l_k$, then of
$l_{k-1}$, down to $l_1$, where the stack tokens of a literal $(n, p)$ are the literal marker of
polarity $p$ followed by the bits of the binary encoding of $n$ (least significant bit first,
empty for $n = 0$) in reverse order.
