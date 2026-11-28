# The Hochschild–Serre spectral sequence

This node is still to be broken down. Let $G$ be a profinite group, $H$ a closed normal subgroup and $A$ a discrete
$G$-module. There is a first quadrant spectral sequence of
[cohomology](cohomology-with-discrete-coefficients.md) groups

$$
E_2^{pq} = H^p(G/H, H^q(H, A)) \Rightarrow H^{p+q}(G, A),
$$

the Hochschild–Serre spectral sequence, with $G/H$ acting on $H^q(H, A)$ as in
[Inflation, restriction and corestriction for profinite groups](inflation-restriction-and-corestriction.md).

## Expansion

This node is still to be broken down. A good expansion states and links:

- the spectral sequence of a filtered cochain complex and of a double complex, and its degeneration criteria
  (Neukirch–Schmidt–Wingberg, Chapter II, §§1–3, pp. 97–110);
- the double complex $C^{pq} = C^p(G/H, H^0(H, X^q(G, A)))$ of the proof of (2.4.1), whose columns are acyclic
  because $H^0(H, X^q)$ is an [induced](induced-modules-are-cohomologically-trivial.md) $G/H$-module, and the
  identification of its $E_2$-terms and abutment;
- the edge maps and the five term sequence they give, matching the
  [five term exact sequence](five-term-exact-sequence.md).

## Depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  the cohomology groups
- [Inflation, restriction and corestriction for profinite groups](inflation-restriction-and-corestriction.md),
  for the action of $G/H$ on $H^q(H, A)$

## Proof depends on

- [Induced modules are cohomologically trivial](induced-modules-are-cohomologically-trivial.md), for the
  acyclicity of the columns of the double complex

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter II, §4, Theorem (2.4.1) and its
  proof, pp. 111–112; Chapter II, §§1–3 (table of contents, pp. 97–110).
