# The ripple-carry adder subtracts

Let $x$ and $y$ be $n$-bit words and let $\bar y$ be the
bitwise complement of $y$. Evaluate the $n$-bit ripple-carry adder, with XOR, AND and OR gates, on
the bits of $x$, the bits of $\bar y$ and carry in $1$. Then for every $i < n$, output $i$ is bit
$i$ (counting from the least significant bit $0$) of $x - y$ modulo $2^n$.
