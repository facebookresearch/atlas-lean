# Bases expressing x ∧ ¬y

For a list $B$ of natural codes, $B$ expresses $x \wedge \neg y$ when every entry of $B$ is below $16$ and some valid expression over $u_0, u_1$ whose connectives are codes in $B$ (the [well-formedness test](well-formed-2-6.md) on $(2, B, \text{tokens})$) is true exactly when $u_0$ is true and $u_1$ is false. The bound applies to every entry, used or not: code $4$ computes $x \wedge \neg y$, so $[4]$ expresses it, but $[4, 20]$ admits no witness, although $20$ is unused and has the same low four truth-table bits.
