# Dyck words over $k$ bracket pairs and the Dyck language $D_k$

Fix $k \in \mathbb{N}$. The bracket alphabet has the letters $(i, \mathrm{open})$ and $(i, \mathrm{close})$ for $i \in \{0, \dots, k-1\}$: the opening and the closing bracket of kind $i$. The Dyck words over $k$ bracket pairs are the smallest set of words over this alphabet such that

- the empty word $\varepsilon$ is a Dyck word;
- if $w_1$ and $w_2$ are Dyck words, so is their concatenation $w_1 w_2$;
- if $w$ is a Dyck word and $i < k$, then $(i, \mathrm{open})\, w\, (i, \mathrm{close})$ is a Dyck word.

The Dyck language $D_k$ is the set of Dyck words over $k$ bracket pairs.

## Sources

- N. Chomsky and M. P. Schützenberger, "The algebraic theory of context-free languages", in *Computer Programming and Formal Systems*, North-Holland, 1963, 118-161.
