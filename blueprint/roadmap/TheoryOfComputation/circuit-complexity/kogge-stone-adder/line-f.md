# Gates of the final level

Gate $j < 3n$ of the final level of the $n$-bit adder with $K$
Kogge-Stone levels serves bit $i = \lfloor j/3 \rfloor$. Write $G_i$ and $P_i$ for the generate and
propagate gates of bit $i$ after the $K$ levels, $p_i$ for the propagate gate of bit $i$ at level
$0$, and $c$ for the carry input. If $j \equiv 0 \pmod 3$ the gate computes $P_i \wedge c$; if
$j \equiv 1 \pmod 3$ it computes the carry $c_{i+1} = G_i \vee (P_i \wedge c)$ from $G_i$ and the
previous gate; if $j \equiv 2 \pmod 3$ it computes the sum bit $p_i \oplus c_i$, where $c_0 = c$
and, for $i \ge 1$, $c_i$ is the carry gate of bit $i - 1$.
