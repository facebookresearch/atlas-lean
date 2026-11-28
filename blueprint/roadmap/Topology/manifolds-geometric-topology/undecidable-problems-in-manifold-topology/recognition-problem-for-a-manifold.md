# Algorithmic recognition problem for a manifold

A closed manifold $M$ is algorithmically recognizable when some algorithm decides, for every finite triangulation of a closed manifold of the same dimension given as input, whether the triangulated manifold is homeomorphic to $M$; otherwise $M$ is unrecognizable.

Fix $n \ge 1$. A *triangulated closed $n$-manifold* is a finite abstract simplicial complex $K$ whose geometric realization $|K|$ is a closed $n$-manifold; such complexes are finite combinatorial objects and can be encoded as input to a Turing machine. For a fixed closed $n$-manifold $M$, the *recognition problem for $M$* asks, given a triangulated closed $n$-manifold $K$, whether $|K|$ is homeomorphic to $M$. The manifold $M$ is *recognizable* if this problem is decidable, that is, if some Turing machine halts on every input $K$ and accepts exactly those $K$ with $|K| \cong M$, and *unrecognizable* otherwise.

Variants:

- In the *PL* or *smooth* versions, homeomorphism is replaced by PL homeomorphism or diffeomorphism, the inputs being triangulations of PL manifolds or of smooth manifolds compatible with the smooth structure.
- Some authors restrict the inputs to combinatorial (PL) triangulations, in which the link of every simplex is a PL sphere, or to triangulations of smooth manifolds.
- The *homeomorphism problem* in dimension $n$ asks, for two triangulated closed $n$-manifolds $K_1$ and $K_2$, whether $|K_1| \cong |K_2|$; if some closed $n$-manifold is unrecognizable, this problem is undecidable.

## Depends on

- [Closed manifold, not required to be connected](../closed-topological-manifold.md)
- [Finite abstract simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md)
- [Homeomorphism](../../topological-spaces/homeomorphism.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Remarks

If $M$ admits no triangulation, no input is homeomorphic to $M$, so $M$ is recognizable for the trivial reason that the answer is always no; results on unrecognizability are therefore stated for manifolds $M$ given by a finite triangulation, as in Poonen's formulation, where the fixed manifold is itself a finite simplicial complex. Recognizability depends only on the homeomorphism type of $M$, since any two triangulations of the input can be compared with $M$ through the same algorithm. The last item holds because a decision procedure for the homeomorphism problem, run with a fixed triangulation of $M$ as one of the two inputs, would decide the recognition problem for $M$. In dimension $n \le 3$ the homeomorphism problem, and hence every recognition problem, is decidable by the classification theorems, in dimension $3$ through Perelman's proof of geometrization; that the $3$-sphere is recognizable was shown earlier by Rubinstein and Thompson.

## Sources

- Bjorn Poonen, *Undecidable problems: a sampler*, in: Interpreting Gödel: Critical Essays (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, https://doi.org/10.1017/CBO9780511756306.015, read in the copy arXiv:1204.0299v2, where Section 7.1 ("The homeomorphism problem") states the homeomorphism problem and the problem of recognizing a fixed manifold $M$ for inputs representing manifolds, their restriction by dimension, and their decidability for dimension at most $3$.
- Michael Joswig, Davide Lofano, Frank H. Lutz and Mimi Tsuruga, *Frontiers of sphere recognition in practice*, J. Appl. Comput. Topol. 6 (2022), no. 4, 503–527, https://doi.org/10.1007/s41468-022-00092-8, read in the copy arXiv:1405.3848v4, whose introduction states the sphere recognition problem for finite simplicial complexes and the decidable low-dimensional cases.
- Alexander V. Chernavsky and Vladimir P. Leksine, *Unrecognizability of manifolds*, Ann. Pure Appl. Logic 141 (2006), no. 3, 325–335, https://doi.org/10.1016/j.apal.2005.12.011, cited beside the sources above for the notion of an unrecognizable manifold.
