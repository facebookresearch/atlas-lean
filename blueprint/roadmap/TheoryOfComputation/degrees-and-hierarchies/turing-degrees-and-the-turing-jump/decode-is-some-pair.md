# The definedness predicate, by cases on the tag

Write $\langle a, b \rangle$ for the
pairing bijection $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$ of the Gödel numbering, and say
that a natural number decodes when the computable decoder returns an oracle code on it. Let $t$
and $p$ be natural numbers and write $p = \langle p_1, p_2 \rangle$. Then $\langle t, p \rangle$
decodes if and only if one of the following holds: $t$ is $0$, $1$, $2$, $3$ or $8$ and $p = 0$;
$t$ is $4$, $5$ or $6$ and both $p_1$ and $p_2$ decode; or $t = 7$ and $p$ decodes.

In the recursive cases $t \ge 1$, so $p_1$, $p_2$ and $p$ are strictly smaller than
$\langle t, p \rangle$.

## Sources

- Rogers, *Theory of Recursive Functions and Effective Computability*, §1.6 (Gödel numberings; decoding).
