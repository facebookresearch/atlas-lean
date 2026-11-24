# (g, K)-modules, the Poincaré–Birkhoff–Witt theorem and Harish-Chandra's homomorphism

This node is still to be broken down. It covers the algebra of enveloping algebras and $(\mathfrak{g}, K)$-modules that the
pages on real reductive groups, automorphic forms and theta correspondence use, separately from the analytic theory of
Harish-Chandra modules. Let $\mathfrak{g}$ be a finite-dimensional complex Lie algebra with
[universal enveloping algebra](../../../Algebra/nonassociative-algebras/universal-enveloping-algebra.md) $U(\mathfrak{g})$ and centre $Z(\mathfrak{g})$, and $K$ a compact Lie group
acting on $\mathfrak{g}$, with complexified Lie algebra $\mathfrak{k} \subseteq \mathfrak{g}$.

- **Poincaré–Birkhoff–Witt.** For a basis $X_1, \dots, X_d$ of $\mathfrak{g}$, the ordered monomials
  $X_1^{a_1} \cdots X_d^{a_d}$ form a basis of $U(\mathfrak{g})$; the associated graded algebra of the degree filtration is the
  symmetric algebra $S(\mathfrak{g})$, and $Z(\mathfrak{g})$ is the subalgebra of $\mathrm{ad}\,\mathfrak{g}$-invariants.
- **$(\mathfrak{g}, K)$-modules.** A $(\mathfrak{g}, K)$-module is a vector space with compatible actions of $\mathfrak{g}$ and $K$:
  it is a direct sum of finite-dimensional continuous $K$-modules, the two actions of $\mathfrak{k}$ agree, and
  $k X v = \mathrm{Ad}(k)(X) k v$. It is admissible if each irreducible representation of $K$ occurs with finite
  multiplicity, and a Harish-Chandra module if it is admissible and finitely generated over $U(\mathfrak{g})$.
- **Finitely generated $Z(\mathfrak{g})$-finite modules** (Harish-Chandra). For $(\mathfrak{g}, K)$ the pair of a real reductive
  group, a finitely generated $(\mathfrak{g}, K)$-module annihilated by an ideal of finite codimension of $Z(\mathfrak{g})$ is
  admissible.
- **Harish-Chandra's homomorphism.** For a real parabolic subgroup with Levi decomposition $\mathfrak{p} = \mathfrak{l} \oplus \mathfrak{n}$,
  there is a homomorphism $\nu \colon Z(\mathfrak{g}) \to Z(\mathfrak{l})$ with $z \in \nu(z) + U(\mathfrak{g})\mathfrak{n}$, and
  $Z(\mathfrak{l})$ is a finitely generated module over $\nu(Z(\mathfrak{g}))$.

## Expansion

A good expansion has statement pages for the Poincaré–Birkhoff–Witt theorem and the centre of $U(\mathfrak{g})$, definition
pages for $(\mathfrak{g}, K)$-modules, admissibility and Harish-Chandra modules, and statement pages for Harish-Chandra's
admissibility of finitely generated $Z(\mathfrak{g})$-finite modules and for the homomorphism $\nu$ and its finiteness, each
citing the sources below with locators. The finiteness of $Z(\mathfrak{l})$ over $\nu(Z(\mathfrak{g}))$ comes from the
Harish-Chandra isomorphisms $Z(\mathfrak{g}) \cong S(\mathfrak{h})^W$ and $Z(\mathfrak{l}) \cong S(\mathfrak{h})^{W_L}$ for a Cartan
subalgebra $\mathfrak{h} \subseteq \mathfrak{l}$.

## Depends on

- [Universal enveloping algebra of a Lie algebra](../../../Algebra/nonassociative-algebras/universal-enveloping-algebra.md), for $U(\mathfrak{g})$
- [Smooth vectors and K-finite vectors of continuous representations](../../lie-and-topological-representations/smooth-and-k-finite-vectors.md), for $K$-finite vectors and the compact group $K$

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- P. Etingof, "Lie groups and Lie algebras", lecture notes, arXiv:2201.09397 (version 5), <https://arxiv.org/abs/2201.09397>: Definition 12.1 and Proposition 12.4 ($U(\mathfrak{g})$, its centre as the invariants), §13.1, Theorem 13.1
  (Poincaré–Birkhoff–Witt).
- P. Etingof, "Representations of Lie groups", lecture notes, arXiv:2401.01446 (version 3), <https://arxiv.org/abs/2401.01446>: §5.2, Definition 5.7, p. 31 ($(\mathfrak{g}, K)$-modules, admissibility, Harish-Chandra modules) and Exercise 5.8;
  §14.1 (the Harish-Chandra isomorphism).
- A. Borel, "Automorphic forms on reductive groups", lecture notes (Park City),
  <http://homepages.math.uic.edu/~rtakloo/papers/borel/borel3.pdf>: §7.4 (c) (the homomorphism $\nu \colon Z(\mathfrak{g}) \to Z(\mathfrak{l}_P)$ with $z \in \nu(z) + U(\mathfrak{g}).\mathfrak{n}_P$,
  and, "by a theorem of Harish-Chandra", $Z(\mathfrak{l}_P)$ finitely generated over $Z(\mathfrak{g})$).
- R. Howe, "Transcending classical invariant theory", J. Amer. Math. Soc. 2 (1989), 535–552,
  <https://doi.org/10.1090/S0894-0347-1989-0985172-6>: §1, p. 536 ($(\mathfrak{g}, K)$-modules after Dixmier) and p. 547
  (a finitely generated quasisimple $(\mathfrak{g}', K')$-module is admissible, "a general result [D]", J. Dixmier,
  *Enveloping algebras*, North-Holland, 1977).
