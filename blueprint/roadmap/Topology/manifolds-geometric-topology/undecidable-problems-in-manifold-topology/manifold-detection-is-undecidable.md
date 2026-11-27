# Deciding whether a finite simplicial complex is a manifold is undecidable

There is no algorithm that decides whether a given finite simplicial complex is homeomorphic to a topological manifold. The proof suspends the homology spheres used for Novikov's theorem on sphere recognition.

The *manifold detection problem* takes as input a finite simplicial complex $M$ and asks whether $|M|$ is homeomorphic to a topological manifold.

**Theorem.** There is no algorithm that decides, for a given finite simplicial complex $M$, whether $|M|$ is homeomorphic to a manifold.

Conventions: the input is an arbitrary finite simplicial complex, with no dimension or manifold assumption.

## Depends on

- [Finite abstract simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md)
- [Closed manifold, not required to be connected](../closed-topological-manifold.md)
- [Homeomorphism](../../topological-spaces/homeomorphism.md)

## Proof depends on

- [The n-sphere is algorithmically unrecognizable for n at least five](sphere-recognition-is-undecidable.md)

## Expansion

Fix $d \ge 5$ and a finitely presented group $G$ with undecidable word problem. Novikov's construction gives, for each word $w$, a finite simplicial complex $X_w$ that is a $d$-dimensional homology sphere with fundamental group trivial exactly when $w$ represents $1$; in that case $X_w$ is homeomorphic to $S^d$ by Smale's theorem, and otherwise its fundamental group is nontrivial. The suspension $S X_w$ adds two cone points $a$ and $b$. If $w = 1$, then $X_w \cong S^d$ and $S X_w \cong S^{d+1}$ is a manifold. If $w \ne 1$, then $X_w$ has nontrivial fundamental group, so loops arbitrarily close to $a$ are not null-homotopic in $S X_w \setminus \{a, b\}$, and $S X_w$ is not locally Euclidean at $a$. Hence $S X_w$ is a manifold if and only if $w = 1$, and an algorithm for manifold detection would solve the word problem of $G$.

## Sources

- Bjorn Poonen, *Undecidable problems: a sampler*, in: Interpreting Gödel: Critical Essays (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, https://doi.org/10.1017/CBO9780511756306.015, read in the copy arXiv:1204.0299v2, where the statement and the suspension argument are in Section 7.2 ("Am I a manifold?").
- I. A. Volodin, V. E. Kuznetsov and A. T. Fomenko, *The problem of discriminating algorithmically the standard three-dimensional sphere*, Russian Math. Surveys 29 (1974), no. 5, 71–172, https://doi.org/10.1070/RM1974v029n05ABEH001296, whose appendix contains Novikov's construction, cited beside the source above.
