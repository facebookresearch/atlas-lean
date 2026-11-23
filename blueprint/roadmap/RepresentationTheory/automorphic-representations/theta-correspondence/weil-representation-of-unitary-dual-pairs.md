# Splitting characters and the Weil representation of unitary dual pairs

**Local setting.** Let $F$ be a local field of characteristic $0$, $E/F$ a quadratic field extension
with non-trivial automorphism $x \mapsto \bar x$, and $\varepsilon_{E/F}$ the quadratic character of
$F^\times$ with kernel $\mathrm{N}_{E/F}(E^\times)$, given by
[local class field theory](../../../NumberTheory/p-adic-numbers/local-class-field-theory.md) when $F$ is
non-archimedean and equal to the sign character when $F = \mathbb{R}$. Let $(V, (\ ,\ ))$ be a
non-degenerate [Hermitian space](../../../NumberTheory/quadratic-forms-sums-of-squares/hermitian-local-global-principle.md)
of dimension $m$ over $E$ and $(W, \langle\ ,\ \rangle)$ a non-degenerate skew-Hermitian space of
dimension $n$, and let $\mathrm{U}(V)$ and $\mathrm{U}(W)$ be their isometry groups. The $F$-vector space
$\mathbb{W} = V \otimes_E W$ of dimension $2mn$ is symplectic for
$\langle\langle v_1 \otimes w_1, v_2 \otimes w_2 \rangle\rangle = \tfrac12 \mathrm{tr}_{E/F}\bigl((v_1, v_2)\, \langle w_1, w_2 \rangle\bigr)$,
and $(\mathrm{U}(V), \mathrm{U}(W))$ is a reductive dual pair in $\mathrm{Sp}(\mathbb{W})$: each group is the
centralizer of the other.

1. **Splittings.** Let $\chi_V$ and $\chi_W$ be unitary characters of $E^\times$ with
   $\chi_V|_{F^\times} = \varepsilon_{E/F}^{m}$ and $\chi_W|_{F^\times} = \varepsilon_{E/F}^{n}$. Then
   $\chi_V$ determines a homomorphism $\tilde\iota_{V, \chi_V} \colon \mathrm{U}(W) \to \mathrm{Mp}(\mathbb{W})$
   and $\chi_W$ a homomorphism $\mathrm{U}(V) \to \mathrm{Mp}(\mathbb{W})$ lifting the natural maps to
   $\mathrm{Sp}(\mathbb{W})$, where $\mathrm{Mp}(\mathbb{W})$ is the
   [metaplectic group](metaplectic-group-and-local-weil-representation.md), viewed as an extension by
   $\mathbb{C}^1$. Pulling back the Weil representation $\omega_\psi$ gives the Weil representation
   $\omega_{\psi, \chi} = \omega_{W, V, \chi, \psi}$ of $\mathrm{U}(W) \times \mathrm{U}(V)$, $\chi = (\chi_V, \chi_W)$.
   If $\mu$ is a character of $E^\times$ trivial on $F^\times$, replacing $\chi_V$ by $\mu\chi_V$
   multiplies $\tilde\iota_{V, \chi_V}$ by $\mu' \circ \det$, where $\mu'(x / \bar x) = \mu(x)$.
2. **Siegel parabolic.** If $n = 2k$ and $W$ is split, with $W = Y \oplus Y^*$ for maximal isotropic
   subspaces of dimension $k$, and $\chi_W$ is trivial (allowed, since $\varepsilon_{E/F}^{2k} = 1$),
   then $\omega_{\psi, \chi}$ is realized on $\mathcal{S}(Y^* \otimes_E V)$ with $h \in \mathrm{U}(V)$
   acting by $\varphi(x) \mapsto \varphi(h^{-1} x)$, an element $a$ of the Levi factor $\mathrm{GL}(Y)$ of
   the stabilizer of $Y$ by $\varphi(x) \mapsto \chi_V(\det a)\, \lvert \det a \rvert_E^{m/2}\, \varphi(a^{-1} x)$,
   an element $u$ of its unipotent radical by $\varphi(x) \mapsto \psi(\tfrac12 \langle u(x), x \rangle)\, \varphi(x)$,
   and the Weyl element by a Fourier transform times a root of unity. These are the local components of
   the global formulas of item 3; on the Levi factor of the stabilizer of the diagonal in a doubled space
   the splitting is $\chi_V \circ \det$.

**Global setting.** Let $F$ be a number field, $E/F$ a quadratic extension, $\psi$ a non-trivial character
of $\mathbb{A}_F / F$, viewed as a character of $\mathbb{A}_E$ through $\mathrm{tr}_{E/F}$, and
$\chi_E$ the quadratic character of $\mathbb{A}_F^\times / F^\times$ attached to $E/F$ by the
[global reciprocity law](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reciprocity-law/global-reciprocity-law.md),
whose local components are the characters $\varepsilon_{E_v/F_v}$ above (trivial at the places that
split). Let $U$ be a skew-Hermitian space of dimension $n$ and $V$ a Hermitian space of dimension $m$ over
$E$, and fix [Hecke characters](../../../NumberTheory/zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md)
$\chi_U, \chi_V$ of $\mathbb{A}_E^\times / E^\times$ with $\chi_U|_{\mathbb{A}_F^\times} = \chi_E^{n}$ and
$\chi_V|_{\mathbb{A}_F^\times} = \chi_E^{m}$.

3. **Global Weil representation.** The restricted tensor product of the local Weil representations
   attached to $(\psi_v, \chi_{U,v}, \chi_{V,v})$ is a representation $\omega_{\psi, \chi_U, \chi_V}$ of
   $\mathrm{U}(U)(\mathbb{A}_F) \times \mathrm{U}(V)(\mathbb{A}_F)$ on $\mathcal{S}(X)(\mathbb{A})$ for a Witt
   decomposition $U \otimes_E V = X \oplus Y$, compatible with the splitting over the rational points of
   the [global metaplectic group](global-weil-representation-and-theta-functions.md), with automorphic
   realization $\theta(\varphi)(g, h) = \sum_{x \in X(F)} \omega_{\psi, \chi_U, \chi_V}(g, h)\varphi(x)$. For
   a split skew-Hermitian space $W_n = Y_n \oplus Y_n^*$ of dimension $2n$ in place of $U$, the Weil
   representation of $\mathrm{U}(W_n)(\mathbb{A}_F) \times \mathrm{U}(V)(\mathbb{A}_F)$ attached to
   $(\psi, \chi_V)$ is realized on $\mathcal{S}(Y_n^* \otimes_E V)(\mathbb{A})$ by the formulas of item 2,
   with the adelic absolute value of $\mathbb{A}_E^\times$.
4. **Doubling.** Let $U^-$ be $U$ with its form multiplied by $-1$ and $W_n = U \oplus U^-$, which is split
   of dimension $2n$, with $Y_n = \{(u, u)\}$ and $Y_n^* = \{(u, -u)\}$. Then the restriction to
   $\mathrm{U}(U) \times \mathrm{U}(U^-) = \mathrm{U}(U) \times \mathrm{U}(U)$ of the Weil representation of
   $\mathrm{U}(W_n) \times \mathrm{U}(V)$ attached to $(\psi, \chi_V)$ is
   $\omega_{\psi, \chi_U, \chi_V} \otimes \bigl(\omega_{\psi, \chi_U, \chi_V}^\vee \cdot (\chi_V \circ \det)\bigr)$,
   through an isomorphism $\delta$ with $\delta(\varphi_1 \otimes \overline{\varphi_2})(0) = \langle \varphi_1, \varphi_2 \rangle$
   for $\varphi_1, \varphi_2 \in \mathcal{S}(X)(\mathbb{A})$, where $\langle\ ,\ \rangle$ is the $L^2$ inner product and
   $\overline{\varphi_2}$, the complex conjugate function, is viewed in the contragredient.

## Depends on

- [Metaplectic group and the local Weil representation](metaplectic-group-and-local-weil-representation.md), for $\mathrm{Mp}(\mathbb{W})$ and $\omega_\psi$
- [Global Weil representation and theta functions](global-weil-representation-and-theta-functions.md), for the global metaplectic group, its splitting over the rational points and the theta distribution
- [Local–global principle for Hermitian spaces over a quadratic extension](../../../NumberTheory/quadratic-forms-sums-of-squares/hermitian-local-global-principle.md), for Hermitian spaces
- [Local class field theory: the local Artin map](../../../NumberTheory/p-adic-numbers/local-class-field-theory.md), for the quadratic character $\varepsilon_{E/F}$ with kernel the norms
- [Global reciprocity law](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reciprocity-law/global-reciprocity-law.md), for the quadratic character $\chi_E$ with kernel $F^\times \mathrm{N}_{E/F}(\mathbb{A}_E^\times)$
- [Meromorphic continuation of Hecke L-functions](../../../NumberTheory/zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md), for Hecke characters of $E$

## Proof depends on

- [Metaplectic group and the local Weil representation](metaplectic-group-and-local-weil-representation.md), for the Leray and Rao cocycles through which Kudla constructs the splittings, and the Schrödinger model in item 2

## Sources

- M. Harris, S. S. Kudla and W. J. Sweet, "Theta dichotomy for unitary groups", J. Amer. Math. Soc. 9
  (1996), 941–1004, <https://doi.org/10.1090/S0894-0347-96-00198-1>: introduction, (0.1)–(0.3)
  (the symplectic form and the splittings), §1, (1.4)–(1.8) (the splitting $\tilde\iota_{V, \chi_V}$
  determined by $\chi_V$ and its dependence on $\chi_V$), (1.11)–(1.15) and Lemma 1.3 (the splitting on the
  Levi factor of the stabilizer of the diagonal is $\chi_V \circ \det$). The splittings are due to S. S.
  Kudla, "Splitting metaplectic covers of dual reductive pairs", Israel J. Math. 87 (1994), 361–401.
- S. S. Kudla, "Notes on the local theta correspondence", lecture notes, European School in Group
  Theory, 1996, <https://www.math.toronto.edu/~skudla/castle.pdf>: §II.1 (type I dual pairs, with
  $(D, \iota) = (E, \sigma)$).
- W. T. Gan and S. Takeda, "A proof of the Howe duality conjecture", J. Amer. Math. Soc. 29 (2016),
  473–493, arXiv:1407.1995 (version 4): §2.8 (splitting characters $\chi = (\chi_V, \chi_W)$ and the Weil
  representation $\omega_{W, V, \chi, \psi}$).
- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and
  the Rallis inner product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3):
  §2.1 (the characters $\psi$ and $\chi_E$), §2.8 (the global Weil representation of
  $\mathrm{U}(W_n) \times \mathrm{U}(V)$ and its formulas, with $\chi|_{\mathbb{A}^\times} = \chi_E^{m_0}$,
  $m \equiv m_0 \bmod 2$), §11.2 (the pair $(\chi_U, \chi_V)$ and $\theta(\varphi)(g, h)$) and §11.3 (the
  doubling see-saw and the isomorphism $\delta$, after Kudla, Harris–Kudla–Sweet and J.-S. Li, J. Reine
  Angew. Math. 428 (1992), p. 182).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states related results as `GlobalTheory.Published.KudlaSplittingSplitUnitary`,
  `GlobalTheory.Published.WeilRepresentationUnitaryPair` and
  `GlobalTheory.Published.WeilRepresentationExists`.
