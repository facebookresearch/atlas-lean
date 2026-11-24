# The overflow flag

Let $n \ge 1$ and let $x$ and $y$ be $n$-bit words. Evaluate the $n$-bit
overflow adder, with XOR, AND and OR gates, on the bits of $x$, the bits of $y$ and carry in $0$.
Its last output (output $n + 1$) is $1$ exactly when the two's complement addition $x + y$
overflows, that is, when the sum of the two's complement values of $x$ and $y$ is at least
$2^{n-1}$ or less than $-2^{n-1}$.
