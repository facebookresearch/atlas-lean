# Restriction through Shapiro's lemma for profinite groups

Let $G$ be a profinite group, $H$ a closed subgroup and $A$ a discrete $G$-module. Let
$i \colon A \to \operatorname{Ind}_G^H(A)$ be the injective $G$-homomorphism $(ia)(\sigma) = \sigma a$, into the
induced module of [Shapiro's lemma](../shapiro-s-lemma.md). Then for every $n \ge 0$ the
[restriction](inflation-restriction-and-conjugation.md) is the composite

$$
\operatorname{res}^G_H = \mathrm{sh} \circ i_* \colon H^n(G, A) \longrightarrow H^n(G, \operatorname{Ind}_G^H(A))
\xrightarrow{\ \sim\ } H^n(H, A),
$$

where $i_*$ is the map that $i$ induces on [cohomology](../cohomology-with-discrete-coefficients.md) and
$\mathrm{sh}$ is Shapiro's isomorphism.

For abstract groups this is [Restriction through Shapiro's lemma](restriction-through-shapiro-s-lemma.md).

## Depends on

- [Inflation, restriction and conjugation](inflation-restriction-and-conjugation.md), for
  $\operatorname{res}^G_H$
- [Shapiro's lemma for profinite groups](../shapiro-s-lemma.md), for $\operatorname{Ind}_G^H(A)$ and $\mathrm{sh}$

## Proof depends on

- [Shapiro's lemma for profinite groups](../shapiro-s-lemma.md), for the cochain-level description of
  $\mathrm{sh}$, by which $\mathrm{sh} \circ i_*$ sends a cochain $x$ of $G$ to its restriction to $H$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §6, the homomorphism $i$ before
  Proposition (1.6.5), p. 63, and Proposition (1.6.5), the right-hand diagram, with its proof ("For the restriction
  this is obvious"), pp. 63–64.
