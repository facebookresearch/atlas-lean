# The sum gates

Let $x, y$ be $n$-bit vectors with bits $x_i$, $y_i$, $c$ a carry-in bit
and $K$ a natural number with $n \le 2^K$. Evaluate the gate program of the $n$-bit adder with
$K$ Kogge–Stone levels in the Boolean interpretation of the XOR/AND/OR basis, on the input made
of the bits of $x$, the bits of $y$ and $c$. Then for every $i < n$, gate $3i + 2$ of the final
level is $x_i \oplus y_i \oplus c_i$, where $c_i$ is the carry into bit $i$ of $x + y + c$, true
exactly when $(x \bmod 2^i) + (y \bmod 2^i) + c \ge 2^i$.
