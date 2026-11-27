# Synchronizing matrices over a semiring

A square matrix over a semiring is synchronizing when exactly one column is nonzero and all entries of that column are equal; a finite set of matrices, or the weighted automaton whose transition matrices they are, is synchronizable when some nonempty product of them is synchronizing.

**Definition.** Let $\mathbb{K} = (K, +, \cdot, 0, 1)$ be a [semiring](../semirings-and-formal-power-series.md) and $M \in \mathbb{K}^{n \times n}$. The matrix $M$ is

- *location synchronizing* if there is a (necessarily unique) index $i \in \{1, \dots, n\}$ such that $M_{j,k} \ne 0$ exactly when $k = i$, for all $j, k$; that is, column $i$ contains no zero entry and every other column is zero;
- *synchronizing* if it is location synchronizing and moreover $M_{j,i} = M_{1,i}$ for every $j$, for that index $i$.

A finite set $\mathcal{M} = \{M_1, \dots, M_k\} \subseteq \mathbb{K}^{n \times n}$ is *(location) synchronizable* if some product $M_{i_1} M_{i_2} \cdots M_{i_t}$ with $t > 0$ and $i_1, \dots, i_t \in \{1, \dots, k\}$ is (location) synchronizing. A [weighted automaton](../weighted-automata-over-a-semiring.md) over $\mathbb{K}$ is (location) synchronizable if the set of its transition matrices is. The problems $\mathbb{K}$-$\mathbf{Sync}$ and $\mathbb{K}$-$\mathbf{LocSync}$ ask, given $n > 0$ and a finite set $\mathcal{M}$ of $n \times n$ matrices over $\mathbb{K}$, whether $\mathcal{M}$ is synchronizable, respectively location synchronizable.

Over the Boolean semiring, the matrices of a complete deterministic automaton are $0/1$ matrices with one $1$ per row, and synchronizability is the existence of a reset word of [synchronizing automata](../../../synchronizing-automata/synchronizing-automata-and-reset-words.md). For every nontrivial semiring both problems are $\mathbf{PSPACE}$-hard; they are decidable when $\mathbb{K}$ is locally finite with computable operations, and $\mathbb{K}$-$\mathbf{LocSync}$ is in $\mathbf{PSPACE}$ when $\mathbb{K}$ is positive (zero-sum free and without zero divisors), since then location synchronization depends only on the positions of zero entries.

## Depends on

- [Semirings and formal power series on a free monoid](../semirings-and-formal-power-series.md)
- [Weighted automata over a semiring](../weighted-automata-over-a-semiring.md)

## Proof depends on

None.

## Sources

- S. Iván, "Synchronizing weighted automata", in Z. Ésik and Z. Fülöp (eds.), *Proceedings 14th International Conference on Automata and Formal Languages (AFL 2014)*, Electronic Proceedings in Theoretical Computer Science 151, 2014, pp. 301–313, doi:[10.4204/EPTCS.151.21](https://doi.org/10.4204/EPTCS.151.21); numbering of arXiv:1403.5729v3: Definition 1 (location synchronizing and synchronizing matrices, the problems $\mathbb{K}$-Sync and $\mathbb{K}$-LocSync) and Propositions 1–4 (hardness and the decidable cases).
