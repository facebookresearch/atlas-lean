# Harish-Chandra's classification of the discrete series

Let $G$ be a connected semisimple Lie group with finite centre, $K$ a maximal compact subgroup,
and use the [discrete series and formal degrees](discrete-series-and-formal-degrees.md). The
character of an irreducible unitary representation $\pi$ is the distribution
$\Theta_\pi(f) = \operatorname{trace} \pi(f)$, $f \in C_c^\infty(G)$.

1. **Existence criterion.** $G$ has a non-empty discrete series if and only if it contains a
   compact Cartan subgroup, that is, if and only if $G$ and $K$ have the same rank.
2. **Parametrization.** Suppose $H \subseteq K$ is a compact Cartan subgroup with Lie algebra
   $\mathfrak{h}_0$; let $\Phi$ be the roots of $(\mathfrak{g}, \mathfrak{h})$ for the complexified
   Lie algebras, $\Lambda \subset i\mathfrak{h}_0^*$ the lattice of differentials of characters of
   $H$, $\rho_0$ half the sum of the positive roots for some ordering, and $W$ the Weyl group of
   $(G, H)$, which is also the Weyl group of $(K, H)$; the translate $\Lambda + \rho_0$ does not
   depend on the ordering. An element $\lambda$ is nonsingular if $(\lambda, \alpha) \ne 0$ for all
   $\alpha \in \Phi$. For every nonsingular $\lambda \in \Lambda + \rho_0$ there is exactly one
   invariant eigendistribution $\Theta_\lambda$ on $G$, bounded at infinity, whose restriction to
   the regular elements of $H$ is
   $$(-1)^q \frac{\sum_{w \in W} \varepsilon(w) e^{w\lambda}}{\prod_{\alpha \in \Phi,\ (\alpha, \lambda) > 0} (e^{\alpha/2} - e^{-\alpha/2})}, \qquad q = \tfrac12 \dim G/K.$$
   Each $\Theta_\lambda$ is the character of a discrete series representation $\pi_\lambda$, every
   discrete series representation is some $\pi_\lambda$, and $\Theta_{\lambda_1} = \Theta_{\lambda_2}$
   exactly when $\lambda_1$ and $\lambda_2$ are conjugate under $W$. So the discrete series is
   parametrized by the nonsingular elements of $\Lambda + \rho_0$ modulo $W$.
3. **Formal degrees.** For a suitable normalization of Haar measure, the formal degree of
   $\pi_\lambda$ is $\prod_{\alpha \in \Phi,\ (\alpha, \lambda) > 0} (\alpha, \lambda)/(\alpha, \rho)$,
   where $\rho$ is half the sum of the roots $\alpha$ with $(\alpha, \lambda) > 0$; in particular
   it is a constant multiple of $\lvert \prod_{\alpha > 0} (\lambda, \alpha) \rvert$.

For example, $\mathrm{SU}(p, q)$ is connected and semisimple with finite centre, and its diagonal
matrices, which lie in $K = \mathrm{S}(\mathrm{U}(p) \times \mathrm{U}(q))$, form a compact Cartan
subgroup; so $\mathrm{SU}(p, q)$ has a discrete series. In $\mathrm{U}(p, q)$ the diagonal matrices
of $\mathrm{U}(p) \times \mathrm{U}(q)$ form a compact Cartan subgroup.

## Depends on

- [Discrete series representations and formal degrees](discrete-series-and-formal-degrees.md)
- [Characters, principal series and the Langlands classification for real reductive groups](principal-series-of-real-reductive-groups.md), for characters of irreducible unitary representations, invariant eigendistributions and the notion of being bounded at infinity

## Proof depends on

- [Characters, principal series and the Langlands classification for real reductive groups](principal-series-of-real-reductive-groups.md), for Harish-Chandra's theory of invariant eigendistributions, their local integrability and matching conditions, and the Plancherel theorem

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
  §2 (characters), and §8, Theorem (8.1) (Harish-Chandra's theorem: existence and uniqueness of
  $\Theta_\lambda$, the formal degree $d(\lambda - \rho)$, exhaustion) with (8.2) (the
  parametrization).
- W. Schmid, "On the characters of the discrete series. The Hermitian symmetric case", Invent.
  Math. 30 (1975), 47–144, <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0030>: §1, (1.1)
  (Harish-Chandra's criterion and character formula).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a related result for $\mathrm{U}(p, q)$ as `GlobalTheory.Published.DiscreteSeriesUpqExists`.
