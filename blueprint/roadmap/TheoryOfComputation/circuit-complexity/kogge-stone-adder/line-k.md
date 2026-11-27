# Gates of a Kogge-Stone level

Gate $j < 3n$ of Kogge-Stone level $k + 1$ of the $n$-bit
adder serves bit $i = \lfloor j/3 \rfloor$ and its partner $q$, which is $i - 2^k$ if $2^k \le i$
and $i$ otherwise. Write $G_b$ and $P_b$ for the generate and propagate gates of bit $b$ after
level $k$. If $j \equiv 0 \pmod 3$ the gate computes $P_i \wedge G_q$; if $j \equiv 1 \pmod 3$ it
computes the new generate signal $G_i \vee (P_i \wedge G_q)$ from $G_i$ and the previous gate; if
$j \equiv 2 \pmod 3$ it computes the new propagate signal $P_i \wedge P_q$.
