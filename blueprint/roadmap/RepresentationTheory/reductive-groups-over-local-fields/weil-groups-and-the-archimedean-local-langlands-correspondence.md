# Weil groups of local fields and the archimedean local Langlands correspondence for GLₙ

This node is still to be broken down. It covers the representations of the Weil groups of $p$-adic fields, the Weil
groups of the archimedean fields and the Langlands parameters that the pages on the local Langlands correspondence,
on base change and on archimedean $L$-factors use.

- **Representations of Weil groups of $p$-adic fields.** Let $F$ be a finite extension of $\mathbb{Q}_p$ with residue field
  of order $q$, and let $W_F$ be its Weil group, with its inertia subgroup $I_F$, its geometric Frobenius elements and
  the reciprocity isomorphism $\mathrm{Art}_F \colon F^\times \cong W_F^{\mathrm{ab}}$ of the [Weil group of a p-adic field](../../NumberTheory/algebraic-number-theory/galois-representations/weil-deligne-representations/weil-group-of-a-p-adic-field.md).
  For a finite extension $E/F$, the open subgroup $W_E$ of finite index of $W_F$ lets representations of $W_E$ induce
  to $W_F$. Representations of $W_F$ are continuous and finite dimensional. An unramified representation is one
  trivial on inertia; an unramified semisimple representation of dimension $n$ is determined by the conjugacy class of the image
  of a geometric Frobenius element.
- **Unramified parameters.** Every irreducible representation $\pi$ of $\mathrm{GL}_n(F)$ with a nonzero
  $\mathrm{GL}_n(\mathcal{O}_F)$-fixed vector is the unramified constituent of the representation
  [normalized-induced](representations-of-p-adic-reductive-groups/parabolic-induction-and-jacquet-functors.md) from unramified characters $\chi_1, \dots, \chi_n$ of
  $F^\times$ (Casselman), and is determined by the $S_n$-orbit of $(\chi_1(\varpi), \dots, \chi_n(\varpi))$, its
  [Satake parameter](representations-of-p-adic-reductive-groups/cartan-decomposition-and-satake-isomorphism.md). Its Langlands parameter is the unramified representation
  $\bigoplus_i \chi_i \circ \mathrm{Art}_F^{-1}$ of $W_F$, on which a geometric Frobenius element acts with eigenvalues
  $\chi_1(\varpi), \dots, \chi_n(\varpi)$. This identification of the Satake parameter with the Frobenius class is a
  normalization of the correspondence; it does not follow from the determination of unramified representations by
  Frobenius.
- **Archimedean Weil groups.** $W_{\mathbb{C}} = \mathbb{C}^\times$, and $W_{\mathbb{R}} = \mathbb{C}^\times \cup j\mathbb{C}^\times$ with
  $jzj^{-1} = \bar z$ and $j^2 = -1$, an extension of $\mathrm{Gal}(\mathbb{C}/\mathbb{R})$ by $\mathbb{C}^\times$, topologized so
  that $\mathbb{C}^\times$, with its usual topology, is an open subgroup of index $2$. The isomorphism
  $W_{\mathbb{R}}^{\mathrm{ab}} \cong \mathbb{R}^\times$ sends $z$ to $z \bar z$ and $j$ to $-1$. The normalized absolute values are
  $\lvert x \rvert_{\mathbb{R}} = \lvert x \rvert$ and $\lvert z \rvert_{\mathbb{C}} = z \bar z$. Representations of $W_k$ are continuous, finite
  dimensional and semisimple; discontinuous characters of $\mathbb{C}^\times$ are excluded. The irreducible ones have
  dimension $1$ or $2$: the characters of $k^\times$ through $W_k^{\mathrm{ab}}$, and, for $k = \mathbb{R}$, the
  representations $\tau_{\ell, t}$ for integers $\ell \ge 1$ and $t \in \mathbb{C}$, with a basis $u, u'$ such that
  $re^{i\theta}$ acts by $r^{2t} e^{i\ell\theta}$ on $u$ and by $r^{2t} e^{-i\ell\theta}$ on $u'$, $ju = u'$ and $ju' = (-1)^\ell u$.
- **Archimedean local Langlands correspondence for $\mathrm{GL}_n$** (Langlands). For $k = \mathbb{R}$ or $\mathbb{C}$ there is a
  bijection $\tau \mapsto \pi(\tau)$ from the isomorphism classes of $n$-dimensional representations of $W_k$ onto the
  isomorphism classes of irreducible admissible smooth representations of moderate growth of $\mathrm{GL}_n(k)$
  (equivalently, by Casselman and Wallach, of irreducible admissible $(\mathfrak{g}, K)$-modules). Characters of
  $W_k^{\mathrm{ab}} = k^\times$ correspond to characters of $\mathrm{GL}_1(k)$, and $\tau_{\ell, t}$ to the essentially discrete series
  representation $D_\ell \otimes \lvert \det \rvert^t$ of $\mathrm{GL}_2(\mathbb{R})$, where $D_\ell$ is the discrete series of weight $\ell + 1$, extended
  by the trivial character of the positive scalar matrices. Write each irreducible $\tau_i$ of dimension $n_i$ as
  $\tau_i^\circ \otimes \lvert \cdot \rvert_k^{t_i}$ with $\tau_i^\circ$ bounded, so that $\pi(\tau_i) = \pi(\tau_i^\circ) \otimes \lvert \det \rvert_k^{t_i}$ with determinant exponent $t_i$
  ($t_i = t$ for $\tau_{\ell, t}$ and for $\chi \lvert \cdot \rvert^t$). For $\tau = \bigoplus_{i=1}^r \tau_i$ ordered so that
  $\operatorname{Re} t_1 \ge \dots \ge \operatorname{Re} t_r$, the representation normalized-induced from $\pi(\tau_1) \otimes \dots \otimes \pi(\tau_r)$ on the
  block upper triangular parabolic subgroup is a standard module, and $\pi(\tau)$ is its unique irreducible quotient, the
  Langlands quotient. The twist acts on the positive real scalar matrices $x I_{n_i}$ by $\lvert \det(x I_{n_i}) \rvert_k^{t_i} = \lvert x \rvert_k^{n_i t_i}$, with
  $\lvert x \rvert_{\mathbb{C}} = x^2$, and the central character of $\pi(\tau_i)$ there is this character times a unitary one. In terms of the
  exponent $a_i = n_i t_i$ of $x \mapsto \lvert x \rvert_k^{a_i}$, the condition reads $\operatorname{Re}(a_1)/n_1 \ge \dots \ge \operatorname{Re}(a_r)/n_r$; dividing the determinant exponents by $n_i$
  would give a different, wrong order when blocks of sizes $1$ and $2$ are mixed.
- **Factors.** With $\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\Gamma(s/2)$ and $\Gamma_{\mathbb{C}}(s) = 2(2\pi)^{-s}\Gamma(s)$, there are factors
  $L(s, \tau)$ and $\varepsilon(s, \tau, \psi)$ of representations of $W_k$ (the existence of $\varepsilon$ for all local fields is a theorem of
  Langlands; at the archimedean places both are explicit), multiplicative on direct sums:
  $L(s, \tau \oplus \tau') = L(s, \tau) L(s, \tau')$ and likewise for $\varepsilon$. For instance
  $L(s, \lvert \cdot \rvert_k^r) = \Gamma_k(s + r)$ with the normalized absolute value, and
  $L(s, \tau_{\ell, t}) = \Gamma_{\mathbb{C}}(s + t + \ell/2)$. For representations $\pi$ of $\mathrm{GL}_n(k)$ and $\pi'$ of
  $\mathrm{GL}_m(k)$ the factors of the pair are defined through the correspondence:
  $L(s, \pi \times \pi') = L(s, \tau(\pi) \otimes \tau(\pi'))$ and $\varepsilon(s, \pi \times \pi', \psi) = \varepsilon(s, \tau(\pi) \otimes \tau(\pi'), \psi)$, where $\tau(\pi)$
  is the parameter of $\pi$.

## Expansion

A good expansion has definition pages for the representations of the Weil groups of $p$-adic fields, for the Weil
groups of the archimedean local fields and for unramified parameters, and statement pages for the unramified correspondence, for the archimedean local Langlands correspondence
for $\mathrm{GL}_n$ and for Weil's archimedean $L$- and $\varepsilon$-factors, each citing the sources below with locators.
Langlands's classification of real groups is by $L$-packets; that the packets of $\mathrm{GL}_n(k)$ are single
representations, so that the correspondence is a bijection, is due to Knapp and Zuckerman with Knapp and Stein for
$\mathrm{GL}_n(\mathbb{R})$ and to Želobenko and Naimark for $\mathrm{GL}_n(\mathbb{C})$, as Knapp reports (pp. 401, 405). Knapp's printed order
condition (2.5) divides the exponents by the block sizes while his (2.2b) and (3.4) twist by $\lvert \det \rvert^t$; it holds with $t_j$
read as the central exponent, and the order above is the one for determinant exponents.

## Depends on

- [Weil group of a p-adic field](../../NumberTheory/algebraic-number-theory/galois-representations/weil-deligne-representations/weil-group-of-a-p-adic-field.md), for the Weil group $W_F$ of a finite extension $F$ of $\mathbb{Q}_p$ with its
  topology, its inertia subgroup, its geometric Frobenius elements, the open subgroups $W_E$ of finite index and the
  reciprocity isomorphism $\mathrm{Art}_F \colon F^\times \cong W_F^{\mathrm{ab}}$ sending uniformizers to geometric Frobenius
  elements, which the representations and unramified parameters of this node use
- [Admissible representations of real reductive groups](representations-of-real-reductive-groups/admissible-representations-of-real-reductive-groups.md), for the representations of
  $\mathrm{GL}_n(\mathbb{R})$ and $\mathrm{GL}_n(\mathbb{C})$
- [Casselman–Wallach globalization theorem](representations-of-real-reductive-groups/casselman-wallach-globalization.md), for the equivalence between representations of moderate growth and $(\mathfrak{g}, K)$-modules
- [Discrete series representations and formal degrees](representations-of-real-reductive-groups/discrete-series-and-formal-degrees.md), for the discrete series of $\mathrm{GL}_2(\mathbb{R})$ attached to the two-dimensional parameters
- [Parabolic induction and Jacquet functors](representations-of-p-adic-reductive-groups/parabolic-induction-and-jacquet-functors.md), for normalized parabolic induction of smooth representations of $\mathrm{GL}_n(F)$, in the unramified correspondence
- [Cartan decomposition and Satake isomorphism for special maximal compact subgroups](representations-of-p-adic-reductive-groups/cartan-decomposition-and-satake-isomorphism.md), for the Satake parameters of the unramified representations of $\mathrm{GL}_n(F)$

## Proof depends on

- [Characters, principal series and the Langlands classification for real reductive groups](representations-of-real-reductive-groups/principal-series-of-real-reductive-groups.md), for the Langlands classification by standard modules and their Langlands quotients, which the correspondence specializes to $\mathrm{GL}_n(k)$

## Sources

- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2), for $p$-adic fields: (1.1.6)–(1.1.10) (the Weil group, its topology and
  $\mathrm{Art}_K$, which this node uses), (3.1.5) (restriction and induction along $W_L \subset W_K$), and
  (4.1.1)–(4.1.8) (unramified representations,
  Casselman's theorem, the Satake parameter and the unramified correspondence, normalized through $\mathrm{Art}_K$).
- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 8, §1, pp. 61–62 (the Weil groups $W_{\mathbb{C}}$ and $W_{\mathbb{R}}$ and the arithmetic Langlands
  classification for $\mathrm{GL}_n(k)$, with Casselman–Wallach), and §2, pp. 62–63 (Weil's $L$- and $\varepsilon$-factors,
  $\Gamma_k$, and the factors of pairs through the classification).
- A. W. Knapp, "Local Langlands correspondence: the archimedean case", in *Motives*, Proc. Sympos. Pure Math. 55,
  Part 2, American Mathematical Society, 1994, 393–410: (2.1a–b), p. 399 (the discrete series $D_\ell$), (2.2a–b) and
  Theorem 1, p. 400, Theorems 2 and 5, pp. 403 and 406 (the bijections for $\mathrm{GL}_n(\mathbb{R})$ and $\mathrm{GL}_n(\mathbb{C})$, through the
  Langlands quotients of standard modules, with the parameters $\tau_{\ell, t}$ of (3.3)–(3.4)), pp. 401 and 405 (the singleton
  packets), and (3.6)–(3.8), p. 404 (the factors, Langlands's existence of $\varepsilon$, and the factors of pairs defined by the
  correspondence).
- R. P. Langlands, "On the classification of irreducible representations of real algebraic groups", in
  *Representation theory and harmonic analysis on semisimple Lie groups*, Math. Surveys Monogr. 31, American
  Mathematical Society, 1989, 101–170, the classification by $L$-packets of Langlands parameters, as cited by Cogdell.
