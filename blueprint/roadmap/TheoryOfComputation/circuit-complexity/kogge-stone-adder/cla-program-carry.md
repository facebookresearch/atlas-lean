# The carry gates

Let $x, y$ be $n$-bit vectors, $c$ a carry-in bit and $K$ a natural number
with $n \le 2^K$. Evaluate the gate program of the $n$-bit adder with $K$ Kogge–Stone levels in
the Boolean interpretation of the XOR/AND/OR basis, on the input made of the bits of $x$, the bits
of $y$ and $c$. Then for every $i < n$, gate $3i + 1$ of the final level holds the carry into bit
$i + 1$ of $x + y + c$, which is true exactly when
$(x \bmod 2^{i+1}) + (y \bmod 2^{i+1}) + c \ge 2^{i+1}$.
