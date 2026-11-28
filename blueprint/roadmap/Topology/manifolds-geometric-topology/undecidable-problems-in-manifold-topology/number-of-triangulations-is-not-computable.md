# The number of triangulations of an algorithmically unrecognizable 4-manifold is not computable

For a compact $4$-manifold $M_0$ that no algorithm recognizes among triangulated manifolds, the number $s(N)$ of distinct triangulations of $M_0$ with at most $N$ simplices is not a computable function of $N$.

Here a *triangulation* of a PL manifold $M$ is a finite [abstract simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md) $K$ whose polyhedron $|K|$ is PL homeomorphic to $M$, and simplicially isomorphic complexes are not distinguished. A PL manifold $M_0$ is *algorithmically unrecognizable* if no algorithm decides, given a triangulation $T$ of a manifold $M$, whether $M$ is PL homeomorphic to $M_0$; this is the PL version of the [recognition problem](recognition-problem-for-a-manifold.md).

**Theorem (Nabutovsky and Ben-Av).** Let $M_0$ be a compact four-dimensional PL manifold that cannot be recognized by any algorithm, and for $N \ge 1$ let $s(N)$ be the number of distinct triangulations of $M_0$ with at most $N$ simplices. Then $s$ is not a recursive function.

By Markov's theorem such manifolds exist; the source notes that one can take a manifold diffeomorphic to the $4$-sphere with $46$ attached handles of index two. In the dynamical triangulation model of four-dimensional quantum gravity, $s(N)$ equals the model's partition function at a particular limiting choice of its parameters (with $\Delta\lambda_4 = \infty$ and $\hat N_4 = N$), so the partition function is not computable there either.

## Depends on

- [Finite abstract simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md)
- [Algorithmic recognition problem for a manifold](recognition-problem-for-a-manifold.md)

## Proof depends on

None.

## Expansion

Suppose $s$ were computable, and fix a triangulation $T_0$ of $M_0$. Given a triangulation $T$ of a manifold $M$ with $N$ simplices, compute $s(N)$ and apply all finite sequences of Alexander's stellar moves and their inverses to $T_0$, recording the distinct triangulations of $M_0$ with at most $N$ simplices, until $s(N)$ of them have been found. Since these moves connect any two triangulations of the same compact PL manifold, the list is then complete, and comparing $T$ with each entry up to simplicial isomorphism decides whether $M$ is PL homeomorphic to $M_0$, contradicting unrecognizability. A good expansion links Alexander's theorem that stellar moves connect PL homeomorphic triangulations, and Markov's theorem on the existence of unrecognizable $4$-manifolds, which have no pages here.

## Sources

- A. Nabutovsky and R. Ben-Av, "Noncomputability arising in dynamical triangulation model of four-dimensional quantum gravity", *Communications in Mathematical Physics* 157(1):93–98, 1993, doi:10.1007/BF02098020; read in arXiv:hep-lat/9208014v1: Proposition 2 with its proof, the convention on triangulations, and the remarks on Markov's manifold and on the partition function, in the numbering of that version.
