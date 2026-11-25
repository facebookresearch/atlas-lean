# Code of a URM instruction

The code of an instruction of an unlimited register machine is the natural number
$\langle 0, n \rangle$ for the zero instruction $Z(n)$, $\langle 1, n \rangle$ for the successor
instruction $S(n)$, $\langle 2, \langle m, n \rangle \rangle$ for the transfer instruction $T(m, n)$,
and $\langle 3, \langle m, \langle n, q \rangle \rangle \rangle$ for the jump instruction
$J(m, n, q)$, where $\langle a, b \rangle$ is the pairing function on $\mathbb{N}$, equal to $b^2 + a$ if $a < b$ and to $a^2 + a + b$ otherwise.
