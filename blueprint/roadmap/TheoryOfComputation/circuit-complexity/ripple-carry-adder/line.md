# Gates of the ripple-carry adder

For natural numbers $n$ and $g$ with $g < 5n$, gate $g$ of
the $n$-bit ripple-carry adder is the following binary gate of the arithmetic basis, whose
arguments are among the $2n + 1$ inputs and the $g$ gates before it. Write $g = 5i + r$ with
$0 \le r < 5$, let $a$ be input $i$ and $b$ input $n + i$, and let $c$ be the carry into bit $i$:
input $2n$ if $i = 0$ and gate $5i - 1$ otherwise. Gate $g$ is the XOR gate with first argument
$a$ and second argument $b$ if $r = 0$, the XOR gate with first argument gate $g - 1$ and second
argument $c$ if $r = 1$, the AND gate with first argument $a$ and second argument $b$ if $r = 2$,
the AND gate with first argument gate $g - 3$ and second argument $c$ if $r = 3$, and the OR gate
with first argument gate $g - 2$ and second argument gate $g - 1$ if $r = 4$.
