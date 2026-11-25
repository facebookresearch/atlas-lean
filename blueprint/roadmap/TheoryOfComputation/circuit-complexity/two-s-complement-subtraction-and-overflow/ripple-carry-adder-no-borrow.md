# Carry out of ripple-carry subtraction

Let $x$ and $y$ be $n$-bit words and let $\bar y$ be
the bitwise complement of $y$. Evaluate the $n$-bit ripple-carry adder, with XOR, AND and OR
gates, on the bits of $x$, the bits of $\bar y$ and carry in $1$. Its carry out (output $n$) is $1$
exactly when there is no unsigned borrow in $x - y$, that is, when $y \le x$ as unsigned
integers.
