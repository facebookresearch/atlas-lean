# Carry out of the ripple-carry adder

Let $x, y$ be $n$-bit vectors and $c$ a bit, and
evaluate the $n$-bit ripple-carry adder, with its gates read as Boolean XOR, AND and OR, on the
input whose entry $j$ is bit $j$ of $x$ and entry $n + j$ is bit $j$ of $y$ for $j < n$ (bit $0$
being the least significant), and whose entry $2n$ is $c$. Its output number $n$ (the last,
outputs being numbered from $0$) is the carry out of $x + y + c$: reading $x$ and $y$ as natural
numbers below $2^n$, it is $1$ exactly when $x + y + c \ge 2^n$.
