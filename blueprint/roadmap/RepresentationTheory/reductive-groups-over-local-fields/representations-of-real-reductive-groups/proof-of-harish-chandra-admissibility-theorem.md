# Proof of Harish-Chandra's admissibility theorem

This node is still to be broken down. It covers the proof of Harish-Chandra's admissibility theorem,
item 1 of the page on
[admissible representations of real reductive groups](admissible-representations-of-real-reductive-groups.md),
which the sources cited there quote without proof: every irreducible unitary representation of $G$ has
finite $K$-multiplicities, at most $\dim V_i$ for an irreducible representation $V_i$ of $K$ when $G$ is
connected semisimple with finite centre. The setting is that page's: $G$ the real points of a
Zariski-connected reductive group over $\mathbb{R}$, $K$ a maximal compact subgroup.

- **The route usually quoted.** (a) On the smooth vectors of an irreducible unitary representation the
  centre $Z(\mathfrak{g})$ of the enveloping algebra acts by scalars (Segal; Harish-Chandra's
  quasi-simplicity). This is not the bounded Schur lemma applied verbatim: the elements of
  $Z(\mathfrak{g})$ act by unbounded operators, and one needs a domain argument for them on the smooth
  vectors. (b) Harish-Chandra's theorem that an irreducible quasi-simple representation of a connected
  semisimple group with finite centre on a Hilbert space has each $K$-type with multiplicity at most its
  dimension. (c) The passage from that case to the real points of a Zariski-connected reductive group,
  through the centre and the derived group, and the distinction between topological and infinitesimal
  irreducibility, which must not be exchanged silently.
- **A worked alternative.** Garrett gives a different proof for real linear reductive groups. The
  expansion should take one route with its exact hypotheses, sources and locators.

## Expansion

A good expansion has pages for the action of $Z(\mathfrak{g})$ by scalars on the smooth vectors of an
irreducible unitary representation, for Harish-Chandra's bound on $K$-multiplicities of quasi-simple
irreducible representations, and for the reduction to the stated real points, each with its group and
domain hypotheses and a pinned source.

It also writes out these steps of its own proof:

- the action of $Z(\mathfrak{g})$ by scalars on the smooth vectors of an irreducible unitary representation (Segal; Harish-Chandra), with its domain argument.
- Harish-Chandra's bound $n_i \le \dim V_i$ for irreducible quasi-simple representations of connected semisimple groups with finite centre.
- the reduction (c) from connected semisimple groups with finite centre to the real points of a Zariski-connected reductive group, through the centre, the derived group and the finitely many components, for the theorem in the stated generality.

## Depends on

- [Linear algebraic groups over local fields and their groups of rational points](../linear-algebraic-groups-over-local-fields.md), for the real points of a Zariski-connected reductive group and their maximal compact subgroups
- [Smooth vectors and K-finite vectors of continuous representations](../../lie-and-topological-representations/smooth-and-k-finite-vectors.md), for smooth vectors and $K$-multiplicities
- [Universal enveloping algebra of a Lie algebra](../../../Algebra/nonassociative-algebras/universal-enveloping-algebra.md), for the enveloping algebra of $\mathfrak{g}$ and its centre $Z(\mathfrak{g})$, for quasi-simplicity

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Sources

- P. Etingof, "Representations of Lie groups", lecture notes, arXiv:2401.01446 (version 3): §5.3,
  Theorem 5.13 (maximal compact subgroups of connected linear semisimple groups, unique up to
  conjugation), Theorem 5.15 (Harish-Chandra's admissibility theorem, stated without proof, "see [HC2],
  [Ga]") and Remark 5.16 (the extension to real reductive groups; the universal cover of
  $\mathrm{SL}_2(\mathbb{R})$, which has no nontrivial compact subgroup, is not covered as stated).
- Harish-Chandra, "Representations of semi-simple Lie groups" I, III and IV, Trans. Amer. Math. Soc. 75
  (1953), 185–243, and 76 (1954), 234–253, and Amer. J. Math. 77 (1955), 743–777, cited by Etingof as
  [HC2].
- P. Garrett, "Proving admissibility of irreducible unitaries", notes,
  <https://www-users.cse.umn.edu/~garrett/m/v/proving_admissibility.pdf>, cited by Etingof as [Ga].
- M. F. Atiyah and W. Schmid, "A geometric construction of the discrete series for semisimple Lie
  groups", Invent. Math. 42 (1977), 1–62, <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0042>:
  §2, (2.1) (the bound $n_i \le \dim V_i$ for connected real semisimple Lie groups with finite centre),
  and p. 8 (for an irreducible unitary representation the smooth vectors are dense, the elements of
  $\mathfrak{U}(\mathfrak{g}^{\mathbb{C}})$ act by unbounded operators, "and the center $\mathfrak{Z}$ of
  $\mathfrak{U}(\mathfrak{g}^{\mathbb{C}})$ acts by scalars").
