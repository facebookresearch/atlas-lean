# Gates of the carry-lookahead adder

For natural numbers $n$ and $K$, the gate program of
the $n$-bit adder with $K$ Kogge–Stone levels is the straight-line program over the XOR/AND/OR
basis on $2n + 1$ inputs (the $n$ bits of one summand, the $n$ bits of the other and a carry-in
$c$) made of level $0$ and Kogge–Stone levels $1, \dots, K$, followed by a final level of $3n$
gates. For each bit $i < n$, let $G_i$ and $P_i$ be the generate and propagate gates of bit $i$
after level $K$ and $p_i$ its propagate gate at level $0$. Gate $3i$ of the final level computes
$P_i \land c$, gate $3i + 1$ computes $G_i \lor (P_i \land c)$, and gate $3i + 2$ computes
$p_i \oplus c$ when $i = 0$ and the XOR of $p_i$ with gate $3(i - 1) + 1$ of the final level
otherwise.
