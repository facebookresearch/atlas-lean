# Decoding and re-encoding a coded state gives it back

Let $p$ be a URM program with
register bound $R$, and let $c$ be a coded state: a program counter together with a list of
register contents. If the list has length $R + 1$, then the coded state, with respect to $p$, of
the machine state decoded from $c$ is $c$.
