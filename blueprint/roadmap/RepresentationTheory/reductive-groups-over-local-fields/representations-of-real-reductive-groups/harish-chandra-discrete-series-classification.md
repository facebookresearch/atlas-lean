# Harish-Chandra's classification of the discrete series

Let $G$ be a connected semisimple Lie group with finite centre, $K$ a maximal compact subgroup,
and use the [discrete series and formal degrees](discrete-series-and-formal-degrees.md). The
character of an irreducible unitary representation $\pi$ is the distribution
$\Theta_\pi(f) = \operatorname{trace} \pi(f)$, $f \in C_c^\infty(G)$. Write
$\det(t + 1 - \operatorname{Ad} g) = \sum_{k \ge 0} D_k(g)\, t^{r+k}$ with $r$ the rank of $G$, and
let $G' = \{ g \in G \mid D_0(g) \ne 0 \}$ be the set of regular semisimple elements. An invariant
eigendistribution $\Theta$, which is given by a locally integrable function analytic on $G'$, is
**bounded at infinity** if $\sup_{b \in B \cap G'} \lvert D_0(b) \rvert^{1/2} \lvert \Theta(b) \rvert < \infty$
for every Cartan subgroup $B$ of $G$.

1. **Existence criterion.** $G$ has a non-empty discrete series if and only if it contains a
   compact Cartan subgroup, that is, if and only if $G$ and $K$ have the same rank.
2. **Parametrization.** Suppose $H \subseteq K$ is a compact Cartan subgroup with Lie algebra
   $\mathfrak{h}_0$; let $\Phi$ be the roots of $(\mathfrak{g}, \mathfrak{h})$ for the complexified
   Lie algebras, $\Lambda \subset i\mathfrak{h}_0^*$ the lattice of differentials of characters of
   $H$, $\rho_0$ half the sum of the positive roots for some ordering, and $W$ the Weyl group of
   $(G, H)$, which is also the Weyl group of $(K, H)$; the translate $\Lambda + \rho_0$ does not
   depend on the ordering. An element $\lambda$ is nonsingular if $(\lambda, \alpha) \ne 0$ for all
   $\alpha \in \Phi$. For nonsingular $\lambda$ let $\rho_\lambda$ be half the sum of the roots
   $\alpha$ with $(\alpha, \lambda) > 0$; if $\lambda \in \Lambda + \rho_0$, then
   $w\lambda - \rho_\lambda \in \Lambda$ for every $w \in W$. For every nonsingular
   $\lambda \in \Lambda + \rho_0$ there is exactly one invariant eigendistribution $\Theta_\lambda$ on
   $G$, bounded at infinity, whose restriction to $H \cap G'$ is the function

    $$(-1)^q \frac{\sum_{w \in W} \varepsilon(w) e^{w\lambda - \rho_\lambda}}{\prod_{\alpha \in \Phi,\ (\alpha, \lambda) > 0} (1 - e^{-\alpha})}, \qquad q = \tfrac12 \dim G/K,$$

    in which every exponential is a character of $H$. The sources print it as
    $(-1)^q \sum_{w} \varepsilon(w) e^{w\lambda} / \prod_{(\alpha, \lambda) > 0} (e^{\alpha/2} - e^{-\alpha/2})$,
    whose numerator and denominator need not be defined on $H$ separately when
    $\rho_0 \notin \Lambda$; multiplying both by $e^{-\rho_\lambda}$ gives the expression above.
    Each $\Theta_\lambda$ is the character of a discrete series representation $\pi_\lambda$, every
    discrete series representation is some $\pi_\lambda$, and $\Theta_{\lambda_1} = \Theta_{\lambda_2}$
    exactly when $\lambda_1$ and $\lambda_2$ are conjugate under $W$. So the discrete series is
    parametrized by the nonsingular elements of $\Lambda + \rho_0$ modulo $W$.

3. **Lowest $K$-type** (Schmid; Atiyah–Schmid). Let $\Psi = \{\alpha \in \Phi \mid (\alpha, \lambda) > 0\}$
   and let $\rho_c$ and $\rho_n$ be half the sums of the compact and of the noncompact roots in
   $\Psi$. In the restriction of $\pi_\lambda$ to $K$, the irreducible representation of highest
   weight $\lambda + \rho_n - \rho_c$ occurs exactly once, and every irreducible constituent has a
   highest weight of the form $\lambda + \rho_n - \rho_c + A$ with $A$ a sum of roots in $\Psi$.
   Since $(\lambda + \rho_n - \rho_c + 2\rho_c, \alpha) = (\lambda + \rho_n + \rho_c, \alpha) > 0$ for
   $\alpha \in \Psi$, it follows that $\mu = \lambda + \rho_n - \rho_c$ is the unique highest weight
   of a $K$-type of $\pi_\lambda$ minimizing $\lVert \mu + 2\rho_c \rVert$.
4. **Formal degrees.** For a suitable normalization of Haar measure, the formal degree of
   $\pi_\lambda$ is $\prod_{\alpha \in \Phi,\ (\alpha, \lambda) > 0} (\alpha, \lambda)/(\alpha, \rho)$,
   where $\rho$ is half the sum of the roots $\alpha$ with $(\alpha, \lambda) > 0$; in particular
   it is a constant multiple of $\lvert \prod_{\alpha > 0} (\lambda, \alpha) \rvert$.

For example, $\mathrm{SU}(p, q)$ is connected and semisimple with finite centre, and its diagonal
matrices, which lie in $K = \mathrm{S}(\mathrm{U}(p) \times \mathrm{U}(q))$, form a compact Cartan
subgroup; so $\mathrm{SU}(p, q)$ has a discrete series.

**The groups $\mathrm{U}(p, q)$.** The group $G = \mathrm{U}(p, q)$, $n = p + q$, is reductive
with compact centre $Z \cong \mathrm{U}(1)$, the scalar matrices, and
$G = Z \cdot \mathrm{SU}(p, q)$ with $Z \cap \mathrm{SU}(p, q) = \mu_n$, so
$G \cong (\mathrm{U}(1) \times \mathrm{SU}(p, q))/\mu_n$. An irreducible unitary representation of
$G$ is the same as an irreducible unitary representation $\pi_0$ of $\mathrm{SU}(p, q)$ together
with a character $\chi$ of $\mathrm{U}(1)$ that agrees with the central character of $\pi_0$ on
$\mu_n$; since $Z$ is compact, its matrix coefficients are square-integrable on $G$ exactly when
those of $\pi_0$ are square-integrable on $\mathrm{SU}(p, q)$. So the discrete series of $G$
consists of the representations $\chi \boxtimes \pi_0$ with $\pi_0$ in the discrete series of
$\mathrm{SU}(p, q)$ and $\chi$ compatible on $\mu_n$. The diagonal torus $H \cong \mathrm{U}(1)^n$ of
$K = \mathrm{U}(p) \times \mathrm{U}(q)$ is a compact Cartan subgroup of $G$ with
$\Lambda = \mathbb{Z}^n$ and $\rho_0 = (\tfrac{n-1}{2}, \tfrac{n-3}{2}, \dots, \tfrac{1-n}{2})$ for the
standard ordering, and the Weyl group of $(G, H)$ is $\mathfrak{S}_p \times \mathfrak{S}_q$.
Combining the parametrization for $\mathrm{SU}(p, q)$ with the character $\chi$, the discrete
series of $\mathrm{U}(p, q)$ is parametrized by the $\lambda \in \mathbb{R}^n$ with pairwise
distinct entries and $\lambda_a - \tfrac{n-1}{2} \in \mathbb{Z}$, modulo
$\mathfrak{S}_p \times \mathfrak{S}_q$, and item 3 holds for $\pi_\lambda$ with $K = \mathrm{U}(p) \times
\mathrm{U}(q)$, the $K$-types of $\chi \boxtimes \pi_0$ being those of $\pi_0$ extended by $\chi$.
This description is for $n > 0$. For $n = 0$ the group $\mathrm{U}(0, 0)$ is trivial: its only
irreducible representation, the trivial one, is square-integrable, corresponds to the empty
parameter $\lambda \in \mathbb{R}^0$, and its only $K$-type has the empty highest weight.

## Depends on

- [Discrete series representations and formal degrees](discrete-series-and-formal-degrees.md)
- [Characters, principal series and the Langlands classification for real reductive groups](principal-series-of-real-reductive-groups.md), for characters of irreducible unitary representations and invariant eigendistributions, with Harish-Chandra's theorem that they are given by locally integrable functions analytic on $G'$

## Proof depends on

- [Characters, principal series and the Langlands classification for real reductive groups](principal-series-of-real-reductive-groups.md), for Harish-Chandra's theory of invariant eigendistributions, their local integrability and matching conditions, the Plancherel theorem, and the Atiyah–Schmid construction of the discrete series with Zuckerman's tensoring argument, which proves item 3

## Sources

- H. Hecht and W. Schmid, "A proof of Blattner's conjecture", Invent. Math. 31 (1975), 129–154,
  <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0031>: §1 (compact Cartan subgroups, "Exactly
  in this situation G has a non-empty discrete series [5]", $\Lambda$, $\rho_0$, the invariant
  eigendistributions $\Theta_\lambda$ [4], "Two of these coincide precisely when their parameters
  $\lambda$ are related by an element of W. Each $\Theta_\lambda$ is the character of a discrete
  series representation, and conversely [5]"), where [4] and [5] are Harish-Chandra, "Discrete
  series for semi-simple Lie groups" I and II, Acta Math. 113 (1965), 241–318, and 116 (1966),
  1–111, the original sources.
- M. F. Atiyah and W. Schmid, "A geometric construction of the discrete series for semisimple Lie
  groups", Invent. Math. 42 (1977), 1–62, <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0042>:
  §1 (the discrete series occurs if and only if $\operatorname{rank} G = \operatorname{rank} K$),
  §2 (characters), (4.25) ($\Lambda_\rho$, the lattice of differentials of characters of $H$
  translated by $\rho$), (6.7)–(6.9) ($D_0$, $G'$ and the definition of "bounded at infinity" by
  $\sup_{b \in B \cap G'} \lvert D_0(b) \rvert^{1/2} \lvert \Theta(b) \rvert < \infty$), and §8, Theorem
  (8.1) (Harish-Chandra's theorem: existence and uniqueness of $\Theta_\lambda$, the formal degree
  $d(\lambda - \rho)$, exhaustion) with (8.2) (the parametrization), (8.3)–(8.4) ($\Psi$, $\rho_c$,
  $\rho_n$) and Theorem (8.5) ("the irreducible K-module of highest weight
  $\lambda + \rho_n - \rho_c$ occurs exactly once. Any irreducible constituent of $\pi_\lambda|_K$ has a
  highest weight of the form $\lambda + \rho_n - \rho_c + A$, where A stands for a sum of roots in
  $\Psi$").
- W. Schmid, "On the characters of the discrete series. The Hermitian symmetric case", Invent.
  Math. 30 (1975), 47–144, <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0030>: §1, (1.1)
  (Harish-Chandra's criterion and character formula), and p. 72, after Theorem (3.11) ("both
  numerator and denominator should be multiplied through by $e^\rho$, or $e^{-\rho}$. As the formula
  stands, the exponential terms need not be well-defined").
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the existence part for $\mathrm{U}(p, q)$, with the lowest $K$-type of item 3, as
  `GlobalTheory.Published.DiscreteSeriesUpqExists`: for every strictly decreasing
  $\lambda \in \mathbb{R}^n$ with $\lambda_a - \tfrac{n-1}{2} \in \mathbb{Z}$ there is an irreducible
  unitary representation of $\mathrm{U}(p, q)$ with square-integrable matrix coefficients containing
  the $K$-type $\lambda + \rho_n - \rho_c$, which minimizes $\lVert \mu + 2\rho_c \rVert$ among its
  $K$-types.
