# Synchronizability of weighted automata over ℕ is undecidable

No algorithm decides, given finitely many square matrices over the natural numbers, whether some nonempty product of them has exactly one nonzero column with all entries of that column equal. The same holds over every semiring in which $1$ has infinite additive order.

**Theorem.** The problem $\mathbb{N}$-$\mathbf{Sync}$, which asks, given $n > 0$ and a finite set $\mathcal{M}$ of $n \times n$ matrices over the semiring $(\mathbb{N}, +, \cdot, 0, 1)$, whether $\mathcal{M}$ is [synchronizable](synchronizing-matrices-over-a-semiring.md), is undecidable. Consequently, if $\mathbb{N}$ embeds into a semiring $\mathbb{K}$, that is, if $1$ has infinite order in $(K, +, 0)$, then $\mathbb{K}$-$\mathbf{Sync}$ is undecidable.

By contrast, location synchronizability over $\mathbb{N}$ is in $\mathbf{PSPACE}$, because $\mathbb{N}$ is a positive semiring. Over $\mathbb{Z}$ both synchronizability problems are undecidable, by a reduction from the mortality problem for integer matrices (Proposition 6 of the source).

## Depends on

- [Synchronizing matrices over a semiring](synchronizing-matrices-over-a-semiring.md)
- [Semirings and formal power series on a free monoid](../semirings-and-formal-power-series.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [MPCP is undecidable](../../../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-mpcp.md)

## Expansion

The proof is a polynomial-time reduction from the variant of the Post correspondence problem in which the first pair is fixed: given pairs $(u_1, v_1), \dots, (u_k, v_k)$ of nonempty binary words, is there an index sequence $i_1, \dots, i_t$ with $i_1 = 1$ and $u_{i_1} \cdots u_{i_t} = v_{i_1} \cdots v_{i_t}$? A word $a_{m-1} \cdots a_0 \in \{0, 1\}^+$ is read as the ternary number $\mathrm{int}(a_{m-1} \cdots a_0) = \sum_i (a_i + 1) 3^i$ with the nonzero digits $1$ and $2$, so that $\mathrm{int}$ is injective (the source uses the digits $0$ and $1$, for which $\mathrm{int}(01) = \mathrm{int}(1)$ and the one-pair instance $(01, 1)$, which has no solution, would give a synchronizable set), and the matrices

$$
M(u) = \begin{pmatrix} 3^{|u|} & 0 \\ \mathrm{int}(u) & 1 \end{pmatrix}
$$

satisfy $M(u) M(v) = M(uv)$ and $u \mapsto M(u)$ is injective, which embeds $(\{0, 1\}^+, \cdot)$ into $\mathbb{N}^{2 \times 2}$. The reduction uses $6 \times 6$ matrices over $\mathbb{N}$: block-diagonal matrices $A_i = \mathrm{diag}(M(u_i), M(u_i), M(v_i))$, a matrix $B$ that applies the fixed first pair $(u_1, v_1)$, and a matrix $C$ whose only nonzero entries are $C_{3,1} = C_{5,1} = 1$. For every index sequence, $B A_{i_2} \cdots A_{i_t} C$ has a single nonzero column, with entries $\mathrm{int}(u_1 u_{i_2} \cdots u_{i_t})$ in four rows and $\mathrm{int}(v_1 v_{i_2} \cdots v_{i_t})$ in two, so it is synchronizing exactly when the two words are equal. Conversely, products of the $A_i$ alone are never synchronizing, and if $XCY$ is synchronizing then so is $XC$, which reduces every synchronizing product to one of this form. Thus the instance has a solution starting with the fixed pair if and only if $\{A_1, \dots, A_k, B, C\}$ is synchronizable. A good expansion links a page for the reduction of every synchronizing product to one of the form $B A_{i_2} \cdots A_{i_t} C$, in addition to the linked variant of the Post correspondence problem.

## Sources

- S. Iván, "Synchronizing weighted automata", in Z. Ésik and Z. Fülöp (eds.), *Proceedings 14th International Conference on Automata and Formal Languages (AFL 2014)*, Electronic Proceedings in Theoretical Computer Science 151, 2014, pp. 301–313, doi:[10.4204/EPTCS.151.21](https://doi.org/10.4204/EPTCS.151.21); numbering of arXiv:1403.5729v3: Theorem 2 with its proof, Proposition 4 (location synchronizability over positive semirings) and Proposition 6 with the remark after it (reduction from mortality).
