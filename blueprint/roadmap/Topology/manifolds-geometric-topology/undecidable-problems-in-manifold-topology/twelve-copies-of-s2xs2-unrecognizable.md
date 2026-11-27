# The connected sum of twelve copies of S²×S² is algorithmically unrecognizable

There is no algorithm that decides, given a triangulation of a closed $4$-manifold, whether it is homeomorphic to the connected sum $\#_{12}(S^2 \times S^2)$ of twelve copies of $S^2 \times S^2$. This is Gordon's sharpening of Markov's theorem.

Let $\#_{12}(S^2 \times S^2)$ denote the connected sum of $12$ copies of $S^2 \times S^2$, a closed simply connected smooth $4$-manifold.

**Theorem (Gordon).** There is no algorithm that takes as input a triangulation of a closed $4$-manifold $X$ and decides whether $X$ is homeomorphic to $\#_{12}(S^2 \times S^2)$.

Conventions: the input is a finite simplicial complex whose realization is a closed $4$-manifold; the target manifold is fixed. Markov's argument shows that $\#_k(S^2 \times S^2)$ is unrecognizable whenever a $k$-relator Adjan–Rabin set exists, and earlier work gave $k = 14$; the statement with $k = 12$ is Gordon's, up to homeomorphism. Whether $S^4$ is recognizable is open. Dunfield, Kegel, Li and Ren record that Tancer has announced, in a preprint not yet refereed, an improvement to $\#_9(S^2 \times S^2)$ in the topological category.

## Depends on

- [Algorithmic recognition problem for a manifold](recognition-problem-for-a-manifold.md)
- [Finite abstract simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md)
- [Closed manifold, not required to be connected](../closed-topological-manifold.md)
- [Homeomorphism](../../topological-spaces/homeomorphism.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof has an algebraic and a topological step, each saving one copy. A $k$-relator Adjan–Rabin set is a recursively enumerable set of finite $k$-relator presentations on which triviality of the presented group is undecidable. Algebraically, Gordon modifies his earlier construction (Lemma 2.1) and applies it to Borisov's $12$-relator presentation of a group with unsolvable word problem to obtain a $13$-relator Adjan–Rabin set (Theorem 2.2). Topologically, Markov's construction attaches to the $5$-ball one-handles for the generators, two-handles along the relators with the $0$-framing, and one further two-handle along a trivial circle for each generator, and Markov's lemma (Lemma 3.1) says that the boundary $M_P$ is homeomorphic to $\#_k(S^2 \times S^2)$ exactly when the presented group is trivial. Gordon attaches only $n - 1$ of these $n$ further two-handles, $n$ being the number of generators; if the group is trivial, sliding the relator handles over each other reduces the resulting manifold to the $5$-ball with $k - 1$ two-handles, so its boundary is $\#_{k-1}(S^2 \times S^2)$ exactly when the group is trivial (Lemma 3.2). Theorem 1.1 follows from Theorem 2.2 and Lemma 3.2. A good expansion links the $13$-relator Adjan–Rabin set, Markov's lemma and its modification, which have no pages here.

## Sources

- Cameron McA. Gordon, *On the homeomorphism problem for 4-manifolds*, New Zealand J. Math. 52 (2022), 821–826, https://doi.org/10.53733/205, read in the author copy arXiv:2106.06006v1, whose numbering is used here: the statement is Theorem 1.1 in Section 1, the algebraic step is Lemma 2.1 and Theorem 2.2 in Section 2, and Markov's lemma and its modification are Lemmas 3.1 and 3.2 in Section 3.
- Nathan M. Dunfield, Marc Kegel, Shana Yunsheng Li and Qiuyu Ren, *Uncomputable trisection invariants of 4-manifolds*, preprint, read in the copy arXiv:2608.27811v2, whose Section 2 records Tancer's later preprint on nine copies and its restriction to the topological category.
