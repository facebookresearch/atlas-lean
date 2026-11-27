# Synchronizability of eight 2×2 matrices is undecidable over semirings containing a free semigroup

Over any semiring whose multiplicative monoid contains a copy of the monoid of words over two letters, it is undecidable whether a given two-state deterministic weighted automaton over an eight-letter alphabet, equivalently a set of eight $2 \times 2$ matrices, is synchronizable.

**Theorem.** Let $\mathbb{K}$ be a semiring such that the semigroup $(\{a, b\}^*, \cdot)$ of words embeds into the multiplicative monoid $(K, \cdot, 1)$. Then $\mathbb{K}$-$\mathbf{Sync}$ is undecidable, already for two-state deterministic weighted automata over an alphabet of size $8$, that is, for sets of eight $2 \times 2$ matrices over $\mathbb{K}$ (in the sense of [synchronizing matrices over a semiring](synchronizing-matrices-over-a-semiring.md)).

An example is the semiring $(\mathcal{P}(\Sigma^*), \cup, \cdot, \emptyset, \{\varepsilon\})$ of languages over an alphabet with at least two letters: it is positive, so its location synchronization problem is in $\mathbf{PSPACE}$, while its synchronization problem is undecidable.

## Depends on

- [Synchronizing matrices over a semiring](synchronizing-matrices-over-a-semiring.md)
- [Semirings and formal power series on a free monoid](../semirings-and-formal-power-series.md)

## Proof depends on

- [MPCP is undecidable](../../../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-mpcp.md)

## Expansion

Identify $\{a, b\}^*$ with its image in $K$. For nonempty words $u, v$ put

$$
A(u, v) = \begin{pmatrix} u & 0 \\ 0 & v \end{pmatrix}, \qquad B(u, v) = \begin{pmatrix} u & 0 \\ v & 0 \end{pmatrix}.
$$

Then $A(u_1, v_1) A(u_2, v_2) = A(u_1 u_2, v_1 v_2)$ and $A(u_1, v_1) B(u_2, v_2) = B(u_1 u_2, v_1 v_2)$; no $A(u, v)$ is synchronizing, and $B(u, v)$ is synchronizing exactly when $u = v$. Hence a product of such matrices is synchronizing if and only if, at the first $B$, the accumulated words agree. This reduces the fixed Post correspondence problem with the *last* pair fixed (an index sequence $i_1, \dots, i_t$ with $i_t = 1$ and $u_{i_1} \cdots u_{i_t} = v_{i_1} \cdots v_{i_t}$) to $\mathbb{K}$-$\mathbf{Sync}$ via $\{(u_i, v_i)\} \mapsto \{A(u_i, v_i) : i \le k\} \cup \{B(u_1, v_1)\}$. Reversing all words turns this problem into the variant with the first pair fixed, so it is undecidable; the source uses that it is already undecidable for $k = 7$ pairs, which gives eight matrices.

## Sources

- S. Iván, "Synchronizing weighted automata", in Z. Ésik and Z. Fülöp (eds.), *Proceedings 14th International Conference on Automata and Formal Languages (AFL 2014)*, Electronic Proceedings in Theoretical Computer Science 151, 2014, pp. 301–313, doi:[10.4204/EPTCS.151.21](https://doi.org/10.4204/EPTCS.151.21); numbering of arXiv:1403.5729v3: Proposition 5 with its proof, and the remark after it on the semiring of languages.
