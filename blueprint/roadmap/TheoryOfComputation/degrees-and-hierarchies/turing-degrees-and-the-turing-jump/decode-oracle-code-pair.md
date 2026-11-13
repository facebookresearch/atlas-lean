# The decoder, by cases on the tag

Write $\langle t, p \rangle$ for the pairing of natural
numbers used by the Gödel numbering of oracle codes, $(p_1, p_2)$ for the unpairing of $p$ (so that
$\langle p_1, p_2 \rangle = p$), and $\mathrm{dec}(n)$ for the result of the computable decoder on
$n$, which is either an oracle code or undefined. Then for all natural numbers $t$ and $p$, the
value $\mathrm{dec}\langle t, p \rangle$ is: $\mathsf{zero}$, $\mathsf{succ}$, $\mathsf{left}$,
$\mathsf{right}$ or $\mathsf{oracle}$ when $p = 0$ and $t$ is $0$, $1$, $2$, $3$ or $8$
respectively; $\mathsf{pair}(a, b)$, $\mathsf{comp}(a, b)$ or $\mathsf{prec}(a, b)$ when $t$ is
$4$, $5$ or $6$ respectively and $\mathrm{dec}(p_1) = a$ and $\mathrm{dec}(p_2) = b$ are both
defined; $\mathsf{rfind}(a)$ when $t = 7$ and $\mathrm{dec}(p) = a$ is defined; and undefined in
every other case.

For $t \in \{4, 5, 6, 7\}$ the numbers decoded on the right, $p_1$, $p_2$ and $p$, are at most $p$
and hence strictly below $\langle t, p \rangle$, so this is a recursion on the code number.

## Sources

- Rogers, *Theory of Recursive Functions and Effective Computability*, §1.6 (Gödel numberings; decoding).
