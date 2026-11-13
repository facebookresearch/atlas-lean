# Sum bits of the overflow adder

Let $x$ and $y$ be $n$-bit words. Evaluate the $n$-bit
overflow adder, with XOR, AND and OR gates, on the bits of $x$, the bits of $y$ and carry in $0$.
Then for every $i < n$, output $i$ is bit $i$ (counting from the least significant bit $0$) of
$x + y$ modulo $2^n$.
