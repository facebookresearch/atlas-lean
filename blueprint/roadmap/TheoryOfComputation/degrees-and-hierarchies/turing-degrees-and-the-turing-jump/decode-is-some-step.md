# One step of the course-of-values recursion for definedness

Write $\langle a, b \rangle$
for the pairing bijection $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$ of the Gödel numbering.
The step takes an argument of the unit type, which it ignores, and a list $L$ of natural numbers;
for $i \in \mathbb{N}$ write $L_i$ for the entry of $L$ at position $i$ (counting from $0$), with
$L_i = 0$ when $i$ is at least the length of $L$. Let $m$ be the length of $L$, and write
$m = \langle t, p \rangle$ and $p = \langle p_1, p_2 \rangle$. The step always returns a value,
namely $1$ if one of the following holds and $0$ otherwise: $t$ is $0$, $1$, $2$, $3$ or $8$ and
$p = 0$; $t$ is $4$, $5$ or $6$ and $L_{p_1} = L_{p_2} = 1$; or $t = 7$ and $L_p = 1$.

Applied to the list whose entry at position $k < m$ is $1$ if $k$ decodes to an oracle code and
$0$ otherwise, it returns the corresponding value for $m$, because in the recursive cases $p_1$,
$p_2$ and $p$ are smaller than $m$.

## Sources

- Rogers, *Theory of Recursive Functions and Effective Computability*, §1.6 (Gödel numberings; decoding).
