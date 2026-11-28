# Triangulations of an unrecognizable manifold are not connected within a computable number of moves

For a PL manifold that no algorithm recognizes, no finite set of elementary moves connects every two of its triangulations with at most $N$ simplices by at most $r(N)$ moves, for any computable function $r$.

Triangulations are taken up to simplicial isomorphism, as finite [abstract simplicial complexes](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md) whose polyhedra are PL homeomorphic to the manifold. A finite set of *elementary moves* on the triangulations of a PL manifold $M_0$ assigns to each triangulation finitely many neighboring triangulations of $M_0$; the moves are operations on finite complexes, so the neighbors of a triangulation can be computed from it, as the proof of the source uses when it applies all chains of moves. It is *computationally ergodic* if there is a recursive function $r$ such that for every $N$ any two triangulations of $M_0$ with at most $N$ simplices are joined by a sequence of at most $r(N)$ moves. A PL manifold is *algorithmically unrecognizable* if no algorithm decides, given a triangulation of a manifold $M$, whether $M$ is PL homeomorphic to $M_0$ (the PL [recognition problem](recognition-problem-for-a-manifold.md)).

**Theorem (Nabutovsky and Ben-Av).** Let $M_0$ be a PL manifold that cannot be recognized by any algorithm. Then no finite set of elementary moves on the set of all triangulations of $M_0$ is computationally ergodic.

Consequently, for an ergodic finite set of moves on the triangulations of a compact four-dimensional unrecognizable manifold $M_0$ (the source recalls that the set of moves used in four-dimensional dynamical triangulations is ergodic, as shown by Gross and Varsted), a fixed triangulation $T_0$ and any recursive function $t$, there are arbitrarily large $N$ for which some triangulation of $M_0$ with $N$ simplices cannot be reached from $T_0$ in fewer than $t(N)$ moves. The source applies the theorem to Markov's unrecognizable $4$-manifold, for instance the $4$-sphere with $46$ attached handles of index two, and notes that it would also apply to $S^4$ if $S^4$ is not algorithmically recognizable.

## Depends on

- [Finite abstract simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md)
- [Algorithmic recognition problem for a manifold](recognition-problem-for-a-manifold.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Compact space](../../topological-spaces/compact-space.md)

## Proof depends on

None.

## Expansion

If a computationally ergodic finite set of moves with bound $r$ existed, fix a triangulation $T_0$ of $M_0$ with $N_0$ simplices. Since the bound applies when both endpoints have at most the given number of simplices, applying all move sequences of length at most $r(\max\{N, N_0\})$ to $T_0$, with no size bound on the intermediate triangulations, and keeping the results with at most $N$ simplices would list, in time computable from $N$, every triangulation of $M_0$ with at most $N$ simplices. Comparing a given triangulation $T$ with $N$ simplices against this list up to simplicial isomorphism would then decide whether $|T|$ is PL homeomorphic to $M_0$, contradicting unrecognizability. The source notes that the argument is very similar to the proof of Theorem 5 b) of Acquistapace, Benedetti and Broglia (Inventiones Mathematicae 102, 1990). A good expansion links the decidability of simplicial isomorphism of finite complexes (Lemma 2.16 of Acquistapace, Benedetti and Broglia, which the source cites). The application to Markov's manifold uses, in addition, Markov's unrecognizability theorem.

## Sources

- A. Nabutovsky and R. Ben-Av, "Noncomputability arising in dynamical triangulation model of four-dimensional quantum gravity", *Communications in Mathematical Physics* 157(1):93–98, 1993, doi:10.1007/BF02098020; read in arXiv:hep-lat/9208014v1: Proposition 1 with its proof, the definition of computational ergodicity, and the consequence for ergodic sets of moves stated after it, in the numbering of that version.
