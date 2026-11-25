# Metaplectic group and the local Weil representation

Let $F$, $W$, $H(W)$, $\psi$ and $\rho_\psi$ be as in the
[Stone–von Neumann theorem](stone-von-neumann-theorem.md), with $\rho_\psi$ the smooth model on a space
$S$ if $F$ is non-archimedean and the unitary model if $F$ is archimedean.

1. **Weil representation.** For $g \in \mathrm{Sp}(W)$ there is an automorphism $A(g)$ of the space of
   $\rho_\psi$ (a unitary one in the archimedean case) with
   $A(g)^{-1} \rho_\psi(h) A(g) = \rho_\psi(h^g)$ for all $h \in H(W)$, unique up to a non-zero scalar.
   The pairs $(g, A(g))$ form a group $\mathrm{Mp}(W)$, a central extension of $\mathrm{Sp}(W)$ by
   $\mathbb{C}^\times$ (by $\mathbb{C}^1$ in the unitary setting), and $\omega_\psi(g, A(g)) = A(g)$ is a
   representation of $\mathrm{Mp}(W)$, the Weil representation attached to $\psi$.
2. **Non-archimedean case.** If $F$ is non-archimedean, the extension $\mathrm{Mp}(W)$ does not depend on
   $\psi$ up to canonical isomorphism, and it is obtained from a twofold central extension
   $1 \to \mu_2 \to \mathrm{Mp}^{(2)}(W) \to \mathrm{Sp}(W) \to 1$ by the inclusion
   $\mu_2 \subset \mathbb{C}^\times$. If $\dim_F W \ge 2$ it does not split. The $\mathbb{C}^\times$-extension
   splits over the stabilizer $P_Y$ of every maximal isotropic subspace $Y$, and any two splittings over
   $P_Y$ agree on the kernel $P_Y^1$ of $p \mapsto \det(p|_Y)$.
3. **Schrödinger model.** For a complete polarization $W = X \oplus Y$, write $g \in \mathrm{Sp}(W)$, acting
   on the right on row vectors $(x, y)$, as $\begin{pmatrix} a & b \\ c & d \end{pmatrix}$. Then
   $\omega_\psi(g, A(g))$ acts on $\mathcal{S}(X)$ as a scalar multiple of the operator

    $$r(g)\varphi(x) = \int_{\ker(c) \backslash Y} \psi\bigl(\tfrac12 \langle xa, xb \rangle - \langle xb, yc \rangle + \tfrac12 \langle yc, yd \rangle\bigr)\, \varphi(xa + yc)\, d\mu_g(y),$$

    for the unique Haar measure $d\mu_g$ for which $r(g)$ preserves the $L^2$ norm. In particular the
    Levi elements $m(a)$, $a \in \mathrm{GL}(X)$, act up to scalars by
    $\varphi(x) \mapsto \lvert \det a \rvert^{1/2} \varphi(xa)$, the elements $n(b)$ of the unipotent radical
    of $P_Y$ by $\varphi(x) \mapsto \psi(\tfrac12 \langle x, xb \rangle)\, \varphi(x)$, and the Weyl element
    exchanging $X$ and $Y$ by a Fourier transform.

4. **Real case.** If $F = \mathbb{R}$, then $\mathrm{Sp}(W) \cong \mathrm{Sp}_{2n}(\mathbb{R})$, the Weil
   representation is a unitary representation $\omega$ (the oscillator representation of Shale and Weil)
   of the twofold cover $\widetilde{\mathrm{Sp}}_{2n}(\mathbb{R})$, and in its Fock model the vectors
   finite under the inverse image $\tilde{\mathrm U}(n)$ of the maximal compact subgroup $\mathrm{U}(n)$ form the
   space $\mathcal{P}(\mathbb{C}^n)$ of polynomials on $\mathbb{C}^n$, on which the complexified Lie algebra acts by

    $$\omega(\mathfrak{sp}_{\mathbb{C}}) = \mathrm{span}\{\tfrac12(z_i \partial_j + \partial_j z_i)\} \oplus \mathrm{span}\{z_i z_j\} \oplus \mathrm{span}\{\partial_i \partial_j\},$$

    where $\partial_j = \partial / \partial z_j$; the first summand is the image of the complexified Lie
    algebra of $\mathrm{U}(n)$. Since $\tfrac12(z_i \partial_j + \partial_j z_i) = z_i \partial_j + \tfrac12 \delta_{ij}$, the group
    $\tilde{\mathrm U}(n)$ acts on the polynomials of each degree through genuine representations: the natural
    action twisted by a square root of $\det$, so that a lift of the rotation by $2\pi$ in a coordinate circle
    acts by $-1$. These formulas are for the Fock model attached to $\psi(t) = e^{2\pi i t}$; replacing $\psi$ by
    $\psi^{-1}$ conjugates the representation and reverses the signs of the weights of $\tilde{\mathrm U}(n)$, and the
    types are again genuine.

## Depends on

- [Stone–von Neumann theorem for Heisenberg groups over local fields](stone-von-neumann-theorem.md), for $\rho_\psi$, its uniqueness and its Schrödinger model

## Proof depends on

- [Stone–von Neumann theorem for Heisenberg groups over local fields](stone-von-neumann-theorem.md), for the existence and uniqueness up to scalars of the operators $A(g)$ (item 1), and the unitary form for the normalization of $r(g)$
- [Explicit formulas for the Weil representation](explicit-formulas-for-the-weil-representation.md), for Rao's cocycle and the explicit operators $r(g)$ (item 3), the reduction to a twofold cover, its independence of $\psi$, its non-splitting and the splitting over $P_Y$ (item 2), and the Fock model (item 4)

## Sources

- S. S. Kudla, "Notes on the local theta correspondence", lecture notes, European School in Group
  Theory, 1996, <https://www.math.toronto.edu/~skudla/castle.pdf>: §I.1 (the operators $A(g)$, the
  extension $\widetilde{\mathrm{Sp}}(W)_\psi$ and $\omega_\psi$), Proposition 2.3 and Lemma 2.4 (the
  operators $r(g)$ of the Schrödinger model), §I.3–I.4 with Corollaries 4.8 and 4.9 (independence of
  $\psi$ and the twofold cover via the Rao cocycle), §I.5 (summary), Lemma 6.1 (splitting over $P_Y$) and
  Proposition 6.6 (the extension is non-trivial; the proof restricts to a symplectic plane, so it needs
  $\dim_F W \ge 2$); Kudla's Chapter I treats non-archimedean fields of characteristic different from $2$.
- R. Ranga Rao, "On some explicit formulas in the theory of Weil representation", Pacific J. Math. 157
  (1993), no. 2, <https://doi.org/10.2140/pjm.1993.157.335>: the explicit cocycle and operators for every
  local field of characteristic different from $2$ and every block rank (Theorems 3.5, 4.1 and 5.3).
- D. Prasad, "A brief survey on the theta correspondence", in *Number Theory (Tiruchirapalli, 1996)*,
  Contemp. Math. 210, American Mathematical Society, 1998, 171–193; author's version
  <https://www.math.iitb.ac.in/~dprasad/dp.pdf>: §1 and §1.1 (the metaplectic group as a twofold cover
  for any local field, and the action of generators in the Schrödinger model).
- R. Howe, "Transcending classical invariant theory", J. Amer. Math. Soc. 2 (1989), 535–552,
  <https://doi.org/10.1090/S0894-0347-1989-0985172-6>: §1 (the oscillator representation of the twofold
  cover of $\mathrm{Sp}_{2n}(\mathbb{R})$, after D. Shale and A. Weil) and §2, (2.1)–(2.3) (the Fock
  model).
- A. Weil, "Sur certains groupes d'opérateurs unitaires", Acta Math. 111 (1964), 143–211,
  <https://doi.org/10.1007/BF02391012>, the original construction.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states related results at the real place, with the Gaussian vector and the Fock-model differential
  operators, as `GlobalTheory.Published.MetaplecticRepresentation` and
  `GlobalTheory.Published.RealMetaplecticRepresentation`.
