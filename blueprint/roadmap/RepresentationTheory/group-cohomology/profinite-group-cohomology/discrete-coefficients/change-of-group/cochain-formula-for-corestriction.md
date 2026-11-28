# The cochain formula for corestriction

Let $G$ be a profinite group, $U$ an open subgroup and $A$ a discrete $G$-module, and choose a representative
$\bar c \in c$ of every right coset $c \in U \backslash G$. For $n \ge 0$ define
$\operatorname{cor} \colon C^n(U, A) \to C^n(G, A)$ on homogeneous cochains by

$$
(\operatorname{cor} x)(\sigma_0, \dots, \sigma_n) = \sum_{c \in U \backslash G} \bar c^{-1}\,
x\bigl(\bar c \sigma_0 \overline{c\sigma_0}^{-1}, \dots, \bar c \sigma_n \overline{c\sigma_n}^{-1}\bigr).
$$

Then $\operatorname{cor} x$ is a $G$-equivariant cochain, $\operatorname{cor} \circ \partial = \partial \circ
\operatorname{cor}$, and the induced map $H^n(U, A) \to H^n(G, A)$ is the
[corestriction](corestriction.md) $\operatorname{cor}^U_G$. Equivalently, $\operatorname{cor}^U_G$ is the map on
the homology of the morphism of complexes $N_{G/U} \colon X^\bullet(G, A)^U \to X^\bullet(G, A)^G$ given by the norm
on the standard resolution, under $H^n(U, A) = H^n(X^\bullet(G, A)^U)$; in degree $0$ it is the norm
$N_{G/U} \colon A^U \to A^G$.

## Depends on

- [Corestriction for open subgroups](corestriction.md), for $\operatorname{cor}^U_G$
- [Cohomology of a profinite group with discrete coefficients](../cohomology-with-discrete-coefficients.md), for
  the cochains and the standard resolution

## Proof depends on

- [Shapiro's lemma for profinite groups](../shapiro-s-lemma.md), for the cochain-level description of
  $\mathrm{sh}$ used in the degree-one computation of Proposition (1.6.5)
- [Naturality of the connecting homomorphism](../naturality-of-the-connecting-homomorphism.md), for the dimension
  shifting from degree one: $\nu_*$ commutes with the connecting homomorphisms, and the cochain map
  $\operatorname{cor}$ does by the same cochain-level argument (the proof of Proposition (1.5.2))
- [The long exact cohomology sequence](../long-exact-cohomology-sequence.md) and
  [Induced modules are acyclic](../induced-modules-are-acyclic.md), for the dimension shifting
- [Induced modules are cohomologically trivial](../induced-modules-are-cohomologically-trivial.md), for
  $H^n(U, A) = H^n(X^\bullet(G, A)^U)$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §5, 4. Corestriction, pp. 47–48 (the
  norm on the standard resolution and the cochain formula); Chapter I, §6, Proposition (1.6.5), the left-hand diagram,
  with its proof, pp. 63–64.
