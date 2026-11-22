# Carry out of the carry-lookahead adder

Let $n, K \in \mathbb{N}$ with $n \le 2^K$, let
$x, y$ be $n$-bit vectors and let $c$ be a carry-in bit. Evaluate the $n$-bit Kogge-Stone
carry-lookahead adder with $K$ levels over the Boolean XOR/AND/OR basis on the input that lists
the bits of $x$ from least to most significant, then those of $y$ in the same order, then $c$.
Its output $n$, the last of its $n + 1$ outputs numbered from $0$, is the carry out of
$x + y + c$: it is true exactly when $x + y + c \ge 2^n$, where $x$, $y$ are read as natural
numbers and $c$ counts as $1$ when true.
