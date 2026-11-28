# Inflation, restriction and corestriction for profinite groups

This node is still to be broken down. It covers the maps of [cohomology](cohomology-with-discrete-coefficients.md)
of profinite groups with discrete coefficients under a change of the group: for a compatible pair
$\varphi \colon G' \to G$, $f \colon A \to A'$ the map $H^n(G, A) \to H^n(G', A')$
([Cohomology commutes with direct limits](cohomology-commutes-with-direct-limits.md) states it), and its cases
the conjugation $\sigma_*$, inflation $\inf \colon H^n(G/H, A^H) \to H^n(G, A)$ for a closed normal subgroup $H$,
restriction $\operatorname{res} \colon H^n(G, A) \to H^n(H, A)$ for a closed subgroup $H$, and corestriction
$\operatorname{cor} \colon H^n(U, A) \to H^n(G, A)$ for an open subgroup $U$, with their properties, the action of
$G/H$ on $H^n(H, A)$ for $H$ normal, and the transgression.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the definitions of $\sigma_*$, $\inf$, $\operatorname{res}$ and $\operatorname{cor}$ (Neukirch–Schmidt–Wingberg,
  Chapter I, §5, pp. 45–49), and their functoriality in the module (Proposition (1.5.2));
- their compatibility with cup products (Proposition (1.5.3)), the commutation of $\sigma_*$ with $\inf$,
  $\operatorname{res}$ and $\operatorname{cor}$ (Proposition (1.5.4)), and their behaviour for two closed
  subgroups $V \subseteq U \subseteq G$ (Proposition (1.5.5));
- the double coset formula (Proposition (1.5.6)) and its corollary (1.5.7): for an open subgroup $U$,
  $\operatorname{cor}_G^U \circ \operatorname{res}_U^G = (G : U)$, and for $U$ also normal
  $\operatorname{res}_U^G \circ \operatorname{cor}_G^U = N_{G/U}$;
- the action of $G$ on $H^n(H, A)$ for a closed normal subgroup $H$, on which $H$ acts trivially (Proposition
  (1.6.3)), and the transgression $\operatorname{tg} \colon H^1(H, A)^{G/H} \to H^2(G/H, A^H)$ (Proposition (1.6.6));
- the same maps for continuous cochain cohomology (Chapter II, §7, p. 138).

## Depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  the cohomology groups the maps connect
- [Cohomology commutes with direct limits](cohomology-commutes-with-direct-limits.md), for the maps induced by
  compatible pairs

## Proof depends on

- [Restriction, corestriction, inflation and Tate's theorem in group cohomology](../../restriction-corestriction-inflation-and-tate-s-theorem.md),
  for the finite-group results, from which the profinite ones follow by passing to the limit
- [Cohomology as a direct limit over finite quotients](cohomology-as-a-direct-limit-over-finite-quotients.md),
  for that passage to the limit

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §5, pp. 45–59, Propositions
  (1.5.2)–(1.5.6) and Corollary (1.5.7), p. 51; Chapter I, §6, Propositions (1.6.3) and (1.6.6); Chapter II, §7,
  p. 138.
