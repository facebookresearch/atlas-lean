# (g, K)-modules, the centre of the enveloping algebra and Harish-Chandra's homomorphism

This node is still to be broken down. It covers the algebra of enveloping algebras and $(\mathfrak{g}, K)$-modules that the
pages on real reductive groups, automorphic forms and theta correspondence use, separately from the analytic theory of
Harish-Chandra modules. Let $\mathfrak{g}$ be a finite-dimensional complex Lie algebra with
[universal enveloping algebra](../../../Algebra/nonassociative-algebras/universal-enveloping-algebra.md) $U(\mathfrak{g})$ and centre $Z(\mathfrak{g})$. A compatible pair $(\mathfrak{g}, K)$
consists of $\mathfrak{g}$ and a compact Lie group $K$ acting smoothly on $\mathfrak{g}$ by Lie algebra automorphisms, with an
embedding of its complexified Lie algebra $\mathfrak{k}$ into $\mathfrak{g}$ such that $K$ acts on $\mathfrak{k}$ by the adjoint
representation and the differentiated action of $\mathfrak{k}$ on $\mathfrak{g}$ is the adjoint action through the embedding.

- **Centre.** $Z(\mathfrak{g})$ is the subalgebra of $\mathrm{ad}\,\mathfrak{g}$-invariants of $U(\mathfrak{g})$, and, by the
  [Poincaré–Birkhoff–Witt theorem](../../../Algebra/nonassociative-algebras/poincare-birkhoff-witt-theorem.md), $U(\mathfrak{g})$ is filtered with associated graded algebra the
  symmetric algebra $S(\mathfrak{g})$, so that it is Noetherian.
- **$(\mathfrak{g}, K)$-modules.** A $(\mathfrak{g}, K)$-module is a vector space with compatible actions of $\mathfrak{g}$ and $K$:
  it is a direct sum of finite-dimensional continuous $K$-modules, the two actions of $\mathfrak{k}$ agree, and
  $k X v = (k \cdot X) k v$ for the action of $K$ on $\mathfrak{g}$. It is admissible if each irreducible representation of $K$ occurs with finite
  multiplicity, and a Harish-Chandra module if it is admissible and finitely generated over $U(\mathfrak{g})$.
- **Finitely generated $Z(\mathfrak{g})$-finite modules** (Harish-Chandra). For $(\mathfrak{g}, K)$ the pair of a real reductive
  group, a finitely generated $(\mathfrak{g}, K)$-module annihilated by an ideal of finite codimension of $Z(\mathfrak{g})$ is
  admissible.
- **Harish-Chandra's homomorphism.** For a real parabolic subgroup with Levi decomposition $\mathfrak{p} = \mathfrak{l} \oplus \mathfrak{n}$,
  there is a homomorphism $\nu \colon Z(\mathfrak{g}) \to Z(\mathfrak{l})$ with $z \in \nu(z) + U(\mathfrak{g})\mathfrak{n}$, and
  $Z(\mathfrak{l})$ is a finitely generated module over $\nu(Z(\mathfrak{g}))$.

## Expansion

A good expansion has a statement page for the centre of $U(\mathfrak{g})$, definition pages for compatible pairs,
$(\mathfrak{g}, K)$-modules, admissibility and Harish-Chandra modules, and statement pages for Harish-Chandra's admissibility of
finitely generated $Z(\mathfrak{g})$-finite modules and for the homomorphism $\nu$ and its finiteness, each citing the sources
below with locators. Howe states the admissibility for a quasisimple module: for a connected group, one on which the
whole centre $Z(\mathfrak{g})$ acts by scalars; for a disconnected group $E$, one on which only the subalgebra of $Z(\mathfrak{g})$ invariant
under the adjoint action of all of $E$ acts by scalars. On the complexified standard representation of $\mathrm{O}(2)$ a reflection
permutes the two infinitesimal characters of the Lie algebra, while the invariant subalgebra acts by scalars. A
finitely generated module $M$ annihilated by an ideal of finite codimension of $Z(\mathfrak{g})$ is the direct sum of finitely
many generalized eigenspaces $M_\chi$ for characters $\chi$ of $Z(\mathfrak{g})$, but a disconnected $K$ need not preserve them, since
it acts on $Z(\mathfrak{g})$: for the standard representation of $\mathrm{O}(2)$, a reflection swaps the two eigenlines of the Lie
algebra. The identity component $K^\circ$ acts trivially on $Z(\mathfrak{g})$, so each $M_\chi$ is a $(\mathfrak{g}, K^\circ)$-module, with a finite
filtration by the submodules $\mathfrak{m}_\chi^i M_\chi$, $\mathfrak{m}_\chi$ the kernel of $\chi$. The subquotients are finitely generated, since
$U(\mathfrak{g})$ is Noetherian, with $Z(\mathfrak{g})$ acting by scalars, hence admissible for $K^\circ$, and so is $M$. As $K/K^\circ$ is finite,
$\dim \mathrm{Hom}_K(\tau, M) \le \dim \mathrm{Hom}_{K^\circ}(\tau, M) < \infty$ for every irreducible representation $\tau$ of $K$, so $M$ is
admissible for $K$. The finiteness of $Z(\mathfrak{l})$ over $\nu(Z(\mathfrak{g}))$ comes from the
Harish-Chandra isomorphisms $Z(\mathfrak{g}) \cong S(\mathfrak{h})^W$ and $Z(\mathfrak{l}) \cong S(\mathfrak{h})^{W_L}$ for a Cartan
subalgebra $\mathfrak{h} \subseteq \mathfrak{l}$.

## Depends on

- [Universal enveloping algebra of a Lie algebra](../../../Algebra/nonassociative-algebras/universal-enveloping-algebra.md), for $U(\mathfrak{g})$
- [Poincaré–Birkhoff–Witt theorem](../../../Algebra/nonassociative-algebras/poincare-birkhoff-witt-theorem.md), for the filtration of $U(\mathfrak{g})$ and its associated graded algebra
- [Smooth vectors and K-finite vectors of continuous representations](../../lie-and-topological-representations/smooth-and-k-finite-vectors.md), for $K$-finite vectors and the compact group $K$

## Proof depends on

- [Poincaré–Birkhoff–Witt theorem](../../../Algebra/nonassociative-algebras/poincare-birkhoff-witt-theorem.md), for the Noetherian property of $U(\mathfrak{g})$, used in the reduction to quasisimple modules

## Sources

- P. Etingof, "Lie groups and Lie algebras", lecture notes, arXiv:2201.09397 (version 5), <https://arxiv.org/abs/2201.09397>: Definition 12.1 and Proposition 12.4 ($U(\mathfrak{g})$, its centre as the invariants).
- P. Etingof, "Representations of Lie groups", lecture notes, arXiv:2401.01446 (version 3), <https://arxiv.org/abs/2401.01446>: §5.2, Definition 5.7, p. 31 ($(\mathfrak{g}, K)$-modules, admissibility, Harish-Chandra modules) and Exercise 5.8;
  §14.1 (the Harish-Chandra isomorphism).
- A. Borel, "Automorphic forms on reductive groups", lecture notes (Park City),
  <http://homepages.math.uic.edu/~rtakloo/papers/borel/borel3.pdf>: §7.4 (c) (the homomorphism $\nu \colon Z(\mathfrak{g}) \to Z(\mathfrak{l}_P)$ with $z \in \nu(z) + U(\mathfrak{g}).\mathfrak{n}_P$,
  and, "by a theorem of Harish-Chandra", $Z(\mathfrak{l}_P)$ finitely generated over $Z(\mathfrak{g})$).
- R. Howe, "Transcending classical invariant theory", J. Amer. Math. Soc. 2 (1989), 535–552,
  <https://doi.org/10.1090/S0894-0347-1989-0985172-6>: §1, p. 536 ($(\mathfrak{g}, K)$-modules after Dixmier; quasisimplicity, through
  the centre for a connected group and through its $\mathrm{Ad}\, E$-invariant subalgebra for a disconnected group $E$) and p. 547
  (a finitely generated quasisimple $(\mathfrak{g}', K')$-module, on which $Z(U(\mathfrak{g}'))^{K'}$ acts by scalars, is admissible, "a
  general result [D]", J. Dixmier, *Enveloping algebras*, North-Holland, 1977).
