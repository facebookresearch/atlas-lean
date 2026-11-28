# Cup products for profinite groups

This node is still to be broken down. It covers the cup product
$H^p(G, A) \times H^q(G, B) \to H^{p+q}(G, A \otimes B)$ of the
[cohomology](cohomology-with-discrete-coefficients.md) of a profinite group $G$ with discrete coefficients, and
the cup product $H^p_{\mathrm{cts}}(G, A) \times H^q_{\mathrm{cts}}(G, B) \to H^{p+q}_{\mathrm{cts}}(G, C)$ of
[continuous cohomology](../continuous-cochain-cohomology/continuous-cohomology.md) induced by a continuous
$G$-pairing $A \times B \to C$, given on homogeneous cochains by
$(f \cup g)(\sigma_0, \dots, \sigma_{p+q}) = f(\sigma_0, \dots, \sigma_p) \cdot g(\sigma_p, \dots, \sigma_{p+q})$.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the cochain identity $\partial(a \cup b) = (\partial a) \cup b + (-1)^p\, a \cup \partial b$ (Proposition (1.4.1)) and
  the resulting cup product on cohomology, with $H^0$ the tensor product of invariants;
- its functoriality in the modules (Proposition (1.4.2)), its compatibility with the connecting homomorphisms of
  exact sequences that stay exact after tensoring (Proposition (1.4.3)), its associativity and skew
  commutativity (Proposition (1.4.4)), and the versions for a pairing of modules (Proposition (1.4.5) and
  Corollary (1.4.6));
- its compatibility with $\sigma_*$, inflation, restriction and corestriction, including
  $\operatorname{cor}(\alpha \cup \operatorname{res}\beta) = (\operatorname{cor}\alpha) \cup \beta$ (Proposition (1.5.3));
- the cup product for continuous cochain cohomology (Chapter II, §7, pp. 137–138), which has the same properties.

## Depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  the cohomology groups and cochains
- [Continuous cohomology](../continuous-cochain-cohomology/continuous-cohomology.md), for the continuous cochain
  version

## Proof depends on

- [The long exact cohomology sequence](long-exact-cohomology-sequence.md), for the compatibility with the
  connecting homomorphisms
- [Inflation, restriction and conjugation](change-of-group/inflation-restriction-and-conjugation.md) and
  [Corestriction for open subgroups](change-of-group/corestriction.md), for the maps in the compatibilities with the
  change of group (Proposition (1.5.3))

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §4, pp. 36–44, Propositions
  (1.4.1)–(1.4.5) and Corollary (1.4.6); Chapter I, §5, Proposition (1.5.3); Chapter II, §7, the cup product of
  continuous cochains, pp. 137–138.
