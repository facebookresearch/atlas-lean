# The n-sphere is algorithmically unrecognizable for n at least five

For every $n \ge 5$ there is no algorithm that decides, given a finite simplicial complex triangulating a closed $n$-manifold, even one that is a homology $n$-sphere, whether it is homeomorphic to the $n$-sphere. This is S. P. Novikov's theorem.

A *homology $n$-sphere* is a closed $n$-manifold whose integral singular homology is isomorphic to that of $S^n$.

**Theorem (Novikov).** Let $n \ge 5$. There is an effectively constructible sequence of finite simplicial complexes $\Sigma_i$, $i \in \mathbb{N}$, such that each $|\Sigma_i|$ is a homology $n$-sphere, each $\Sigma_i$ is either a PL $n$-sphere or has nontrivial fundamental group (and so is not homeomorphic to $S^n$), and no algorithm decides, for every given $\Sigma_i$, which of the two cases holds. Consequently $S^n$ is unrecognizable in the sense of the [recognition problem](recognition-problem-for-a-manifold.md): no algorithm decides, for a triangulated closed $n$-manifold $K$, whether $|K|$ is homeomorphic to $S^n$.

Conventions: the dimension $n$ is fixed and the complex is the input. Since the inputs $\Sigma_i$ are manifolds, the theorem also gives the weaker statement for arbitrary finite $n$-dimensional simplicial complexes as inputs. The same construction shows that for every fixed closed $n$-manifold $M$ with $n \ge 5$, recognizing $M$ is undecidable. For $n \le 2$ sphere recognition is elementary, and for $n = 3$ it is decidable by the work of Rubinstein and Thompson.

## Depends on

- [Algorithmic recognition problem for a manifold](recognition-problem-for-a-manifold.md)
- [Finite abstract simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md)
- [Closed manifold, not required to be connected](../closed-topological-manifold.md)
- [Integral singular homology](../../algebraic-topology/hurewicz-theorem/integral-homology.md)
- [Homeomorphism](../../topological-spaces/homeomorphism.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../../GroupTheory/presentations-and-decision-problems/word-problem-for-groups/novikov-unsolvable.md)
- [Hurewicz theorem for (n−1)-connected spaces, n ≥ 2](../../algebraic-topology/hurewicz-theorem/hurewicz-theorem.md)
- [Topological Poincaré conjecture in dimensions at least 5](../poincar-conjecture/poincare-high-dim-topological.md)

## Expansion

The proof reduces from the word problem. Fix a finitely presented group $G$ with undecidable word problem. From $G$ and a word $w$ one builds a finitely presented group $G_w$ with $H_1(G_w) = H_2(G_w) = 0$ that is trivial exactly when $w$ represents $1$ in $G$. These homological conditions are necessary and sufficient for $G_w$ to be the fundamental group of a homology $n$-sphere, and one can effectively construct a finite simplicial complex $X_w$ triangulating such a homology sphere with $\pi_1(X_w) \cong G_w$. If $w$ represents $1$, then $X_w$ is a simply connected homology sphere, hence homeomorphic to $S^n$ by the high-dimensional Poincaré conjecture; otherwise $\pi_1(X_w)$ is nontrivial. An algorithm recognizing $S^n$ would therefore solve the word problem of $G$. A good expansion links the construction of $G_w$, the realization of such groups as fundamental groups of triangulated homology spheres, and Whitehead's theorem, which with the Hurewicz theorem turns a simply connected homology sphere into a homotopy sphere; these have no pages here. A detailed proof is in Novikov's appendix to the survey of Volodin, Kuznetsov and Fomenko.

## Sources

- Jiří Matoušek, Martin Tancer and Uli Wagner, *Hardness of embedding simplicial complexes in $\mathbb{R}^d$*, J. Eur. Math. Soc. (JEMS) 13 (2011), no. 2, 259–295, https://doi.org/10.4171/JEMS/252, read in the copy arXiv:0807.0336v2: Theorem 3.1 ("Novikov") at the start of Section 3 ("Undecidability: Proof of Theorem 1.1") states the theorem in the form above, citing the appendix of Nabutovsky's paper for a detailed proof.
- Bjorn Poonen, *Undecidable problems: a sampler*, in: Interpreting Gödel: Critical Essays (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, https://doi.org/10.1017/CBO9780511756306.015, read in the copy arXiv:1204.0299v2: Section 7.1 ("The homeomorphism problem") states that recognizing $S^d$ is undecidable for every $d \ge 5$, that the same holds for every fixed compact $d$-manifold, and sketches the proof through the complexes $X_w$.
- Michael Joswig, Davide Lofano, Frank H. Lutz and Mimi Tsuruga, *Frontiers of sphere recognition in practice*, J. Appl. Comput. Topol. 6 (2022), no. 4, 503–527, https://doi.org/10.1007/s41468-022-00092-8, read in the copy arXiv:1405.3848v4: Theorem 1 in its introduction states the weaker form for arbitrary $d$-dimensional complexes, followed by the decidable low-dimensional cases.
- I. A. Volodin, V. E. Kuznetsov and A. T. Fomenko, *The problem of discriminating algorithmically the standard three-dimensional sphere*, Russian Math. Surveys 29 (1974), no. 5, 71–172, https://doi.org/10.1070/RM1974v029n05ABEH001296, which contains Novikov's proof, cited beside the sources above.
- Alexander V. Chernavsky and Vladimir P. Leksine, *Unrecognizability of manifolds*, Ann. Pure Appl. Logic 141 (2006), no. 3, 325–335, https://doi.org/10.1016/j.apal.2005.12.011, cited beside the sources above.
