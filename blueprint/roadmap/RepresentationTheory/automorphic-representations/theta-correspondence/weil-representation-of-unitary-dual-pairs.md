# Splitting characters and the Weil representation of unitary dual pairs

**Local setting.** Let $F$ be a local field of characteristic $0$ and $E$ a quadratic étale $F$-algebra
with non-trivial automorphism $x \mapsto \bar x$: either a quadratic field extension, or $E = F \times F$
with $\overline{(a, b)} = (b, a)$. Let $\varepsilon_{E/F}$ be the character of $F^\times$ with kernel
$\mathrm{N}_{E/F}(E^\times)$: the quadratic character given by
[local class field theory](../../../NumberTheory/p-adic-numbers/local-class-field-theory.md) when $E$ is a
field and $F$ is non-archimedean, the sign character when $F = \mathbb{R}$ and $E = \mathbb{C}$, and the trivial
character when $E = F \times F$. Let $(V, (\ ,\ ))$ be a non-degenerate
[Hermitian space](../../../NumberTheory/quadratic-forms-sums-of-squares/hermitian-local-global-principle.md)
of dimension $m$ over $E$ and $(W, \langle\ ,\ \rangle)$ a non-degenerate skew-Hermitian space of
dimension $n$, both forms $E$-linear in the first variable and conjugate-linear in the second, and let
$\mathrm{U}(V)$ and $\mathrm{U}(W)$ be their isometry groups. On the $F$-vector space
$\mathbb{W} = V \otimes_E W$ of dimension $2mn$ (with $av \otimes w = v \otimes aw$ for $a \in E$), the form

$$\langle\langle v_1 \otimes w_1, v_2 \otimes w_2 \rangle\rangle = \tfrac12 \mathrm{tr}_{E/F}\bigl((v_1, v_2)\, \langle w_1, w_2 \rangle\bigr)$$

is well defined, $F$-bilinear, alternating and non-degenerate. If $m, n \ge 1$, $\mathrm{U}(V)$ and
$\mathrm{U}(W)$ embed in $\mathrm{Sp}(\mathbb{W})$ as a reductive dual pair: each group is the centralizer of the
other. If $E = F \times F$, then $V = V_0 \times V_0^\vee$ and $W = W_0 \times W_0^\vee$ for $F$-vector spaces
$V_0$, $W_0$ of dimensions $m$, $n$, the groups $\mathrm{U}(V)$ and $\mathrm{U}(W)$ are identified with $\mathrm{GL}(V_0)$ and
$\mathrm{GL}(W_0)$ through their actions on the first components, and $\mathbb{W} = (V_0 \otimes_F W_0) \times (V_0^\vee \otimes_F W_0^\vee)$,
with $\mathrm{GL}(V_0) \times \mathrm{GL}(W_0)$ acting on $V_0 \otimes_F W_0 = \mathrm{Hom}_F(W_0^\vee, V_0)$ by $T \mapsto g\, T\, {}^t h$ and on the
second component by the contragredient action. Fix a non-trivial continuous unitary character $\psi$ of $F$.

1. **Splittings.** Let $\chi_V$ and $\chi_W$ be unitary characters of $E^\times$ with
   $\chi_V|_{F^\times} = \varepsilon_{E/F}^{m}$ and $\chi_W|_{F^\times} = \varepsilon_{E/F}^{n}$ (splitting characters).
   For $m, n \ge 1$, $\chi_V$ determines a homomorphism $\tilde\iota_{V, \chi_V} \colon \mathrm{U}(W) \to \mathrm{Mp}(\mathbb{W})$
   and $\chi_W$ a homomorphism $\mathrm{U}(V) \to \mathrm{Mp}(\mathbb{W})$ lifting the natural maps to
   $\mathrm{Sp}(\mathbb{W})$, where $\mathrm{Mp}(\mathbb{W})$ is the
   [metaplectic group](metaplectic-group-and-local-weil-representation.md) viewed as an extension by
   $\mathbb{C}^1$, the pushout of the twofold cover; in general these splittings do not take values in the
   twofold cover. Pulling back the Weil representation $\omega_\psi$ gives the Weil representation
   $\omega_{\psi, \chi} = \omega_{W, V, \chi, \psi}$ of $\mathrm{U}(W) \times \mathrm{U}(V)$, $\chi = (\chi_V, \chi_W)$.
   If $\mu$ is a character of $E^\times$ trivial on $F^\times$, replacing $\chi_V$ by $\mu\chi_V$
   multiplies $\tilde\iota_{V, \chi_V}$ by $\mu' \circ \det$, where $\mu'(x / \bar x) = \mu(x)$ (by Hilbert's theorem
   90, $x \mapsto x/\bar x$ maps $E^\times$ onto the norm-one elements). If $E = F \times F$, the Weil
   representation is realized on the Schwartz–Bruhat functions on the Lagrangian $V_0 \otimes_F W_0 = \mathrm{Hom}_F(W_0^\vee, V_0)$,
   where, up to twists by characters of $\det$, $(g, h)$ acts by $\varphi(T) \mapsto \varphi(g^{-1}\, T\, {}^t h^{-1})$ (on $m \times n$
   matrices, in bases); the matrix model $\varphi(x) \mapsto \varphi(g^{-1} x\, h')$ of Mínguez
   is obtained by identifying $\mathrm{GL}(W_0)$ with $\mathrm{GL}_n(F)$ through the contragredient, $h' = {}^t h^{-1}$. (The model on
   $\mathrm{Hom}_F(W_0, V_0)$ with $T \mapsto g T h^{-1}$ would be wrong: the element $(a, a^{-1})$, $a \in F^\times$, acts trivially on
   $\mathbb{W}$ but would dilate $\mathrm{Hom}_F(W_0, V_0)$ by $a^2$.)
2. **Siegel parabolic.** If $n = 2k$ and $W$ is split, with $W = Y \oplus Y^*$ for maximal isotropic
   subspaces of dimension $k$, and $\chi_W$ is trivial (allowed, since $\varepsilon_{E/F}^{2k} = 1$),
   then $\omega_{\psi, \chi}$ is realized on $\mathcal{S}(Y^* \otimes_E V)$ with $h \in \mathrm{U}(V)$
   acting by $\varphi(x) \mapsto \varphi(h^{-1} x)$, an element $a$ of the Levi factor $\mathrm{GL}(Y)$ of
   the stabilizer of $Y$ by $\varphi(x) \mapsto \chi_V(\det a)\, \lvert \det a \rvert_E^{m/2}\, \varphi(a^{-1} x)$,
   an element $u \in \mathrm{Hom}(Y^*, Y)$ of its unipotent radical by
   $\varphi(x) \mapsto \psi(\tfrac12 \langle\langle u(x), x \rangle\rangle)\, \varphi(x)$, with the $F$-valued form
   $\langle\langle\ ,\ \rangle\rangle$ above, and the Weyl element by a Fourier transform times a root of unity. These
   are the local components of the global formulas of item 3; on the Levi factor of the stabilizer of the
   diagonal in a doubled space the splitting is $\chi_V \circ \det$.

**Global setting.** Let $F$ be a number field, $E/F$ a quadratic extension, $\psi$ a non-trivial character
of $\mathbb{A}_F / F$, viewed as a character of $\mathbb{A}_E$ through $\mathrm{tr}_{E/F}$, and
$\chi_E$ the quadratic character of $\mathbb{A}_F^\times / F^\times$ with kernel $F^\times \mathrm{N}_{E/F}(\mathbb{A}_E^\times)$,
which has index $2$ by the
[global reciprocity law](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reciprocity-law/global-reciprocity-law.md);
its local components are the characters $\varepsilon_{E_v/F_v}$ for the étale algebras $E_v = E \otimes_F F_v$
(trivial at the places that split). Let $U$ be a skew-Hermitian space of dimension $n \ge 1$ and $V$ a
Hermitian space of dimension $m \ge 1$ over $E$, and fix
[Hecke characters](../../../NumberTheory/zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md)
$\chi_U, \chi_V$ of $\mathbb{A}_E^\times / E^\times$ with $\chi_U|_{\mathbb{A}_F^\times} = \chi_E^{n}$ and
$\chi_V|_{\mathbb{A}_F^\times} = \chi_E^{m}$.

3. **Global Weil representation.** Fix an $F$-rational polarization $\mathrm{Res}_{E/F}(U \otimes_E V) = X \oplus Y$ and
   lattices $L_U$, $L_V$. At almost all places $v$ — those where $E$, $\psi_v$, $\chi_{U,v}$ and $\chi_{V,v}$ are unramified, $v$ is
   not dyadic, $L_U$ and $L_V$ are self-dual at $v$, and the tensor lattice splits compatibly with the polarization,
   $L_U \otimes L_V = ((L_U \otimes L_V) \cap X(F_v)) \oplus ((L_U \otimes L_V) \cap Y(F_v))$ — the images under the local splittings of the
   hyperspecial subgroups $K_{U,v}$ and $K_{V,v}$ stabilizing $L_U$ and $L_V$ fix the characteristic function $\varphi_v^\circ$ of
   $(L_U \otimes L_V) \cap X(F_v)$. (Without the compatibility of the polarization with the lattices, the vector fixed by
   the hyperspecial subgroups is the lattice-model vacuum, which need not be this indicator. The whole local groups
   need not fix $\varphi_v^\circ$: on a split hyperbolic factor of positive rank, a Levi element with a uniformizer entry
   carries it to a multiple of the characteristic function of another lattice; for an inert pair of lines both
   groups are $E_v^1$ and equal their hyperspecial subgroups.) The restricted tensor
   product of the local Weil representations with respect to the $\varphi_v^\circ$, at all places including the split
   ones, is a representation $\omega_{\psi, \chi_U, \chi_V}$ of $\mathrm{U}(U)(\mathbb{A}_F) \times \mathrm{U}(V)(\mathbb{A}_F)$ on
   $\mathcal{S}(X)(\mathbb{A})$: the pullback of the Weil representation of the $\mathbb{C}^1$-extension of the
   [global metaplectic group](global-weil-representation-and-theta-functions.md) along the product of the local
   splittings, which agrees on the rational points with its splitting over $\mathrm{Sp}(F)$, with automorphic realization
   $\theta(\varphi)(g, h) = \sum_{x \in X(F)} \omega_{\psi, \chi_U, \chi_V}(g, h)\varphi(x)$. For a split
   skew-Hermitian space $W_n = Y_n \oplus Y_n^*$ of dimension $2n$ in place of $U$, the Weil representation
   of $\mathrm{U}(W_n)(\mathbb{A}_F) \times \mathrm{U}(V)(\mathbb{A}_F)$ attached to $(\psi, \chi_V)$ is realized on
   $\mathcal{S}(Y_n^* \otimes_E V)(\mathbb{A})$ by the formulas of item 2, with the adelic absolute value of
   $\mathbb{A}_E^\times$.
4. **Doubling.** Let $U^-$ be $U$ with its form multiplied by $-1$ and $W_n = U \oplus U^-$, which is split
   of dimension $2n$, with $Y_n = \{(u, u)\}$ and $Y_n^* = \{(u, -u)\}$. Then the restriction to
   $\mathrm{U}(U)(\mathbb{A}) \times \mathrm{U}(U^-)(\mathbb{A}) = \mathrm{U}(U)(\mathbb{A}) \times \mathrm{U}(U)(\mathbb{A})$ of the Weil
   representation of $\mathrm{U}(W_n)(\mathbb{A}) \times \mathrm{U}(V)(\mathbb{A})$ attached to $(\psi, \chi_V)$ is
   $\omega_{\psi, \chi_U, \chi_V} \otimes \bigl(\overline{\omega_{\psi, \chi_U, \chi_V}} \cdot (\chi_V \circ \det)\bigr)$, through
   an isometry $\delta$ of $L^2$ models, defined on the completed tensor product of the Schwartz spaces
   (with self-dual measures), with
   $\delta(\varphi_1 \otimes \overline{\varphi_2})(0) = \langle \varphi_1, \varphi_2 \rangle$ for
   $\varphi_1, \varphi_2 \in \mathcal{S}(X)(\mathbb{A})$, where $\langle\ ,\ \rangle$ is the $L^2$ inner product and
   $\overline{\varphi_2}$ is the complex conjugate function.

## Depends on

- [Metaplectic group and the local Weil representation](metaplectic-group-and-local-weil-representation.md), for $\mathrm{Mp}(\mathbb{W})$ and $\omega_\psi$
- [Global Weil representation and theta functions](global-weil-representation-and-theta-functions.md), for the global metaplectic group, its splitting over the rational points and the theta distribution
- [Local–global principle for Hermitian spaces over a quadratic extension](../../../NumberTheory/quadratic-forms-sums-of-squares/hermitian-local-global-principle.md), for Hermitian spaces
- [Local class field theory: the local Artin map](../../../NumberTheory/p-adic-numbers/local-class-field-theory.md), for the quadratic character $\varepsilon_{E/F}$ with kernel the norms
- [Global reciprocity law](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reciprocity-law/global-reciprocity-law.md), for the quadratic character $\chi_E$ with kernel $F^\times \mathrm{N}_{E/F}(\mathbb{A}_E^\times)$
- [Meromorphic continuation of Hecke L-functions](../../../NumberTheory/zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md), for Hecke characters of $E$

## Proof depends on

- [Explicit formulas for the Weil representation](explicit-formulas-for-the-weil-representation.md), for Kudla's construction of the splittings from the Leray and Rao cocycles, their restriction to Levi factors, the character twists through Hilbert's theorem 90, the compatibility of the local splittings and the product formula giving the global splitting, and the doubling intertwiner $\delta$
- [Metaplectic group and the local Weil representation](metaplectic-group-and-local-weil-representation.md), for the Schrödinger model in item 2

## Sources

- W. T. Gan, "Automorphic forms and the theta correspondence", lecture notes, arXiv:2303.14918 (version
  1): §2.2 (étale quadratic algebras, the symplectic form $\mathrm{Tr}(\langle -, - \rangle_V \otimes \langle -, - \rangle_W)$ and
  the dual pair), §2.5 (Kudla's splittings by splitting characters, change of characters through
  $E^1 \to E^\times/F^\times$), §2.13 (the split case: $\mathrm{GL}_m \times \mathrm{GL}_n$ acting, up to twists by
  characters, on $\mathcal{S}(\mathrm{M}_{m \times n}(F))$, after A. Mínguez), §§3.2–3.3 (the global Weil representation
  as a restricted tensor product with respect to the vectors fixed by the hyperspecial subgroups). Gan's form
  has no factor $\tfrac12$: his character $\psi_{\mathrm{Gan}}$ corresponds to $t \mapsto \psi(t/2)$ here.
- A. Mínguez, "Correspondance de Howe explicite : paires duales de type II", Ann. Sci. Éc. Norm. Supér. (4)
  41 (2008), 717–741: §§1.1–1.2 and (1.4) with its footnote (the matrix model of the type II pair and its
  conventions).
- Y. Liu, "Theta correspondence for almost unramified representations of unitary groups",
  arXiv:2105.14223 (version 1): Definition 3.1 and Lemma 3.2 (the characteristic function of the self-dual
  lattice is fixed by the hyperspecial subgroups).
- M. Harris, S. S. Kudla and W. J. Sweet, "Theta dichotomy for unitary groups", J. Amer. Math. Soc. 9
  (1996), 941–1004, <https://doi.org/10.1090/S0894-0347-96-00198-1>: introduction, (0.1)–(0.3)
  (the symplectic form, for non-archimedean $F$, and the splittings), §1, (1.4)–(1.8) (the splitting $\tilde\iota_{V, \chi_V}$
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
  Angew. Math. 428 (1992), p. 182, (12)–(13), where $\delta$ is an isometry of $L^2$ models).
- D. Prasad, "Theta correspondence for unitary groups", Pacific J. Math. 194 (2000), 427–438,
  <https://doi.org/10.2140/pjm.2000.194.427>: §1 (the choice of splitting characters, and the splittings into
  the $\mathbb{C}^1$-extension rather than the twofold cover).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states related results as `GlobalTheory.Published.KudlaSplittingSplitUnitary` (a $p$-adic field $E$ and a
  split skew-Hermitian space), `GlobalTheory.Published.WeilRepresentationUnitaryPair` and
  `GlobalTheory.Published.WeilRepresentationExists` (specialized global data).
