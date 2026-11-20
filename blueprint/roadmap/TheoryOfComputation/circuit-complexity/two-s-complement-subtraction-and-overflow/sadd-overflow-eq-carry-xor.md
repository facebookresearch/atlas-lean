# Signed overflow is the XOR of the last two carries

Let $n \ge 1$ and let $x$ and $y$ be
$n$-bit words. The two's complement addition $x + y$ overflows (the sum of the two's complement
values of $x$ and $y$ is at least $2^{n-1}$ or less than $-2^{n-1}$) exactly when the carry into
the sign bit $n - 1$ differs from the carry out of it, both carries taken when adding $x$ and $y$
with carry in $0$.
