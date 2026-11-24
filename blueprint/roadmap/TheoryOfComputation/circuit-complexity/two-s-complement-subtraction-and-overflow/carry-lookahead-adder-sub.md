# The carry-lookahead adder subtracts

Let $x$ and $y$ be $n$-bit words, let $\bar y$ be the
bitwise complement of $y$, and let $K$ satisfy $n \le 2^K$. Evaluate the $n$-bit carry-lookahead
adder with $K$ levels, with XOR, AND and OR gates, on the bits of $x$, the bits of $\bar y$ and
carry in $1$. Then for every $i < n$, output $i$ is bit $i$ (counting from the least significant
bit $0$) of $x - y$ modulo $2^n$.
