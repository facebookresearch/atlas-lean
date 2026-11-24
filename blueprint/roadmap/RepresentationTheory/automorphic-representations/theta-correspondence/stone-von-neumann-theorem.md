# Stone–von Neumann theorem for Heisenberg groups over local fields

Let $F$ be a local field of characteristic different from $2$, $(W, \langle\ ,\ \rangle)$ a non-degenerate symplectic
vector space of dimension $2n$ over $F$, and $H(W) = W \oplus F$ its Heisenberg group, with
multiplication

$$(w_1, t_1)(w_2, t_2) = \bigl(w_1 + w_2,\ t_1 + t_2 + \tfrac12 \langle w_1, w_2 \rangle\bigr).$$

The symplectic group $\mathrm{Sp}(W)$ acts on $H(W)$ by the automorphisms $(w, t)^g = (wg, t)$, which are
trivial on the centre $Z = \{(0, t)\} \cong F$. Let $\psi$ be a non-trivial continuous unitary character
of $F$.

1. **Non-archimedean case.** If $F$ is non-archimedean, there is, up to isomorphism, a unique smooth
   irreducible representation $(\rho_\psi, S)$ of $H(W)$ with central character $\psi$, that is, with
   $\rho_\psi((0, t)) = \psi(t)\, \mathrm{id}_S$ for $t \in F$; it is admissible.
2. **Unitary form.** For every local field $F$ there is, up to unitary equivalence, a unique irreducible
   unitary representation of $H(W)$ on a Hilbert space on which $(0, t)$ acts by $\psi(t)$.
3. **Schrödinger model.** Let $W = X \oplus Y$ be a complete polarization ($X$ and $Y$ maximal
   isotropic), and $\mathcal{S}(X)$ the space of Schwartz–Bruhat functions on $X$. The formula

    $$\rho\bigl((x + y, t)\bigr)\varphi(x_0) = \psi\bigl(t + \langle x_0, y \rangle + \tfrac12 \langle x, y \rangle\bigr)\, \varphi(x_0 + x)$$

    defines a representation of $H(W)$ on $\mathcal{S}(X)$ that preserves the $L^2$ norm for a Haar
    measure on $X$ and extends to the irreducible unitary representation of item 2 on $L^2(X)$. If $F$ is
    non-archimedean, $(\rho, \mathcal{S}(X))$ is a model of $(\rho_\psi, S)$, and $\mathcal{S}(X)$ is the space
    of smooth vectors of $L^2(X)$: the vectors fixed by some compact open subgroup of $H(W)$, depending on
    the vector.

Since $\mathrm{Sp}(W)$ fixes the centre, the representation $h \mapsto \rho_\psi(h^g)$ again has central
character $\psi$, so it is isomorphic to $\rho_\psi$; this is the starting point of the
[Weil representation](metaplectic-group-and-local-weil-representation.md).

## Depends on

- [Smooth and admissible representations of p-adic groups](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md), for smooth, irreducible and admissible representations of the $\ell$-group $H(W)$ when $F$ is non-archimedean

## Proof depends on

- [Induction and Mackey theory for Heisenberg groups](induction-and-mackey-theory-for-heisenberg-groups.md), for the smooth induction from the subgroup $H(Y)$ through which Mœglin, Vignéras and Waldspurger construct and characterize the smooth model (items 1 and 3), and for the Stone–von Neumann–Mackey theorem behind the unitary form (item 2)

## Sources

- S. S. Kudla, "Notes on the local theta correspondence", lecture notes, European School in Group
  Theory, 1996, <https://www.math.toronto.edu/~skudla/castle.pdf>: §I.1, Theorem 1.1 (Stone–von
  Neumann, smooth form) and Remark (i) ("usually stated in terms of unitary representations"; the
  smooth version is taken from C. Mœglin, M.-F. Vignéras and J.-L. Waldspurger, *Correspondances de
  Howe sur un corps p-adique*, Lecture Notes in Math. 1291, Springer, 1987, Chapter 2, Théorème I.2,
  pp. 28–31); §I.2, Lemma 2.1 (the induced model is smooth, irreducible and admissible), Lemma 2.2 (the
  Schrödinger model formula), and the proof of Lemma 2.4 (extension to $L^2(X)$ and the smooth vectors).
- D. Prasad, "A brief survey on the theta correspondence", in *Number Theory (Tiruchirapalli, 1996)*,
  Contemp. Math. 210, American Mathematical Society, 1998, 171–193; author's version
  <https://www.math.iitb.ac.in/~dprasad/dp.pdf>: §1, Theorem 1 (uniqueness, for any local field).
- A. Prasad, "An easy proof of the Stone–von Neumann–Mackey theorem", arXiv:0912.0574 (2009): §4.1
  (statement for the Heisenberg group of a locally compact abelian group), §§4.2–4.3 (proofs), for item 2.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the existence and uniqueness of a smooth irreducible representation with central character $\psi$
  in the non-archimedean case, without the admissibility of item 1, as
  `GlobalTheory.Published.StoneVonNeumann`.
