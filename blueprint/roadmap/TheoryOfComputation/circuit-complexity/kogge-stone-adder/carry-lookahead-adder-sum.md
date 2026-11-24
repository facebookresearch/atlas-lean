# Sum bits of the carry-lookahead adder

Let $x, y$ be $n$-bit vectors, $c$ a carry-in bit
and $K$ a natural number with $n \le 2^K$. Evaluate the $n$-bit Kogge–Stone carry-lookahead adder
with $K$ levels in the Boolean interpretation of the XOR/AND/OR basis, on the input made of the
bits of $x$, the bits of $y$ and $c$. Then for every $i < n$, output $i$ of the adder is bit $i$
(the bit of weight $2^i$) of the sum $x + y + c$ taken modulo $2^n$.
