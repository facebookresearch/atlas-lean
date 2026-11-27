# Induction and Mackey theory for Heisenberg groups

This node is still to be broken down. It covers the induction arguments behind the
[Stone–von Neumann theorem](stone-von-neumann-theorem.md) for the Heisenberg group $H(W)$ of a symplectic
space $W$ over a local field $F$ of characteristic different from $2$, with a polarization
$W = X \oplus Y$ and a non-trivial character $\psi$ of $F$.

- **Smooth induction.** For a closed subgroup $H$ of an $\ell$-group $G$, smooth induction and compact induction
  of smooth representations; Frobenius reciprocity in the form that smooth induction is right adjoint to
  restriction (for open $H$, compact induction is moreover left adjoint to restriction; for arbitrary closed
  $H$ it is not, as $H = \{0\} \subset G = \mathbb{Q}_p$ shows).
- **The induced Heisenberg representation.** The character $\psi_Y(y, t) = \psi(t)$ of the abelian subgroup
  $H(Y) = Y \oplus F$ (trivial on $Y$); the smooth representation of $H(W)$ smoothly induced from it, whose
  functions are shown to have compact support modulo $H(Y)$ because of the central character (in compact
  induction this support condition is imposed instead); its realization on the Schwartz–Bruhat functions on $X$;
  its irreducibility and admissibility; and for an arbitrary smooth irreducible representation of $H(W)$ with
  central character $\psi$, the construction of a non-zero $H(Y)$-equivariant functional to $\psi_Y$, through which
  Frobenius reciprocity identifies the representation with the induced one. These are the inputs of the smooth
  existence and uniqueness statements of the Stone–von Neumann theorem, which this node does not restate.
- **Unitary form.** The Stone–von Neumann–Mackey theorem for Heisenberg groups of locally compact abelian
  groups, for strongly continuous unitary representations on which the circle acts tautologically
  ($z \mapsto z \cdot \mathrm{Id}$): the representation on $L^2(L)$ is irreducible, and every such representation is a multiple
  of it; the comparison with $H(W)$ by pushing out its centre $F$ along $\psi$; the identification of $Y$ with the
  Pontryagin dual of $X$ through $\psi$ and the pairing.

## Expansion

A good expansion has pages for smooth and compact induction of representations of $\ell$-groups with the
correct adjunctions, for the irreducibility and the decomposition of the representation induced from a
polarization, and for the unitary Stone–von Neumann–Mackey theorem, each with a precise statement and the
sources below; it should not add a second statement of the classification in the Stone–von Neumann
theorem.

## Depends on

- [Smooth and admissible representations of p-adic groups](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md), for smooth representations of $\ell$-groups

## Proof depends on

- [Additive duality of adeles and the volume of A/K](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/additive-duality-of-adeles.md), for the self-duality $a \mapsto \psi(a\,\cdot)$ of the completions of number fields (its local duality), which identifies $Y$ with the Pontryagin dual of $X$ for local fields of characteristic $0$
- [Pontryagin duality and the self-duality of local fields](../../../Analysis/harmonic-analysis/pontryagin-duality-and-self-duality-of-local-fields.md), for the self-duality $a \mapsto \psi(a\,\cdot)$ of every local field, for every nontrivial character $\psi$ (Poonen, §4.3, Theorem 4.4), for the local fields of positive characteristic that the statement allows, such as $\mathbb{F}_3((t))$; and for Pontryagin duality for locally compact abelian groups, for the unitary form
- [Unitary representations of locally compact groups and representations of compact groups](../../lie-and-topological-representations/unitary-representations-and-representations-of-compact-groups.md), for the decomposition of every strongly continuous unitary representation of a compact abelian group into the orthogonal sum of its character spaces, with arbitrary multiplicities, which A. Prasad (§4.2, p. 4) applies to the given representation restricted to $G \times G^\perp$, for the unitary form; the decomposition of $L^2$ of the group, where each character occurs once, is not enough

## Sources

- S. S. Kudla, "Notes on the local theta correspondence", lecture notes, European School in Group
  Theory, 1996, <https://www.math.toronto.edu/~skudla/castle.pdf>: §I.1, Theorem 1.1 and Remark (i), and
  §I.2, Lemmas 2.1 (i) (compact support modulo $H(Y)$ from the central character), 2.2 and 2.4 (the induced
  model from $H(Y)$, its smoothness, irreducibility and admissibility, and its Schrödinger form), after C. Mœglin, M.-F. Vignéras and J.-L. Waldspurger,
  *Correspondances de Howe sur un corps p-adique*, Lecture Notes in Math. 1291, Springer, 1987, Chapter 2,
  Théorème I.2, pp. 28–31, as cited by Kudla.
- A. Prasad, "An easy proof of the Stone–von Neumann–Mackey theorem", arXiv:0912.0574 (2009): §4.1 (the
  theorem for Heisenberg groups of locally compact abelian groups, with the tautological action of the
  circle), §4.2, p. 4 (groups with compact open subgroups; the given representation decomposed under the compact
  abelian group $G \times G^\perp$ by the Peter–Weyl theorem), §4.3 ($\mathbb{R}^n$) and §4.4 (general locally compact abelian
  groups); §§4.2–4.3 suffice for local fields.
- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I", Ann. Sci.
  Éc. Norm. Supér. (4) 10 (1977), 441–472, <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §1.8 and
  Proposition 1.9 (b) (for the induction functors defined there, induction is right adjoint to the
  corresponding restriction functor).
