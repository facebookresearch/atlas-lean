# The n-sphere is algorithmically unrecognizable for n at least five

For every $n \ge 5$ there is no algorithm that decides, given a finite $n$-dimensional simplicial complex, whether it is homeomorphic to the $n$-sphere. This is S. P. Novikov's theorem.

**Theorem (Novikov).** Let $n \ge 5$. There is no algorithm that takes as input a finite $n$-dimensional simplicial complex $K$ and decides whether $|K|$ is homeomorphic to the sphere $S^n$.

Conventions: the dimension $n$ is fixed and the complex is the input; the statement says that $S^n$ is an unrecognizable manifold in the sense of the recognition problem. For $n \le 2$ sphere recognition is elementary, and for $n = 3$ it is decidable by the work of Rubinstein and Thompson.

## Depends on

- [Algorithmic recognition problem for a manifold](recognition-problem-for-a-manifold.md)
- [Finite abstract simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md)
- [Homeomorphism](../../topological-spaces/homeomorphism.md)

## Proof depends on

None.

## Expansion

As in Markov's theorem on the homeomorphism problem, the proof reduces from an undecidable problem about finitely presented groups. Novikov constructs from group presentations closed $n$-manifolds with the homology of $S^n$ whose fundamental groups are the presented groups, so that a manifold in the family is a sphere exactly when its fundamental group is trivial; for $n \ge 5$ a simply connected homology sphere is homeomorphic to $S^n$ by the generalized Poincaré conjecture. An algorithm recognizing $S^n$ would then decide triviality for a class of presentations for which this problem is undecidable. A detailed account is in the survey of Volodin, Kuznetsov and Fomenko.

## Sources

- Michael Joswig, Davide Lofano, Frank H. Lutz and Mimi Tsuruga, *Frontiers of sphere recognition in practice*, J. Appl. Comput. Topol. 6 (2022), no. 4, 503–527, https://doi.org/10.1007/s41468-022-00092-8, read in the copy arXiv:1405.3848v4, whose numbering is used here: the statement is Theorem 1 in its introduction, attributed to Novikov, followed by the decidable low-dimensional cases.
- I. A. Volodin, V. E. Kuznetsov and A. T. Fomenko, *The problem of discriminating algorithmically the standard three-dimensional sphere*, Russian Math. Surveys 29 (1974), no. 5, 71–172, https://doi.org/10.1070/RM1974v029n05ABEH001296, which contains Novikov's proof, cited beside the source above.
- Alexander V. Chernavsky and Vladimir P. Leksine, *Unrecognizability of manifolds*, Ann. Pure Appl. Logic 141 (2006), no. 3, 325–335, https://doi.org/10.1016/j.apal.2005.12.011, cited beside the source above.
