# The five term exact sequence

Let $G$ be a profinite group, $H$ a closed normal subgroup and $A$ a discrete $G$-module. With the
[inflation and restriction](change-of-group/inflation-restriction-and-conjugation.md) maps and the
[transgression](change-of-group/transgression.md), the sequence

$$
0 \to H^1(G/H, A^H) \xrightarrow{\inf} H^1(G, A) \xrightarrow{\operatorname{res}} H^1(H, A)^{G/H}
\xrightarrow{\operatorname{tg}} H^2(G/H, A^H) \xrightarrow{\inf} H^2(G, A)
$$

of [cohomology](cohomology-with-discrete-coefficients.md) groups is exact. Moreover, if $n \ge 1$ and
$H^i(H, A) = 0$ for $i = 1, \dots, n - 1$, the sequence

$$
0 \to H^n(G/H, A^H) \xrightarrow{\inf} H^n(G, A) \xrightarrow{\operatorname{res}} H^n(H, A)^{G/H}
\xrightarrow{\operatorname{tg}} H^{n+1}(G/H, A^H) \xrightarrow{\inf} H^{n+1}(G, A)
$$

is exact. In particular inflation followed by restriction is exact at $H^n(G, A)$ in these cases.

For abstract groups and representations, Mathlib has the degree-one case, the exactness of the short complex
`groupCohomology.H1InfRes A S` of inflation and restriction for a normal subgroup `S`
(`groupCohomology.H1InfRes_exact`).

## Depends on

- [Inflation, restriction and conjugation](change-of-group/inflation-restriction-and-conjugation.md), for $\inf$
  and $\operatorname{res}$
- [The action of the quotient on the cohomology of a normal subgroup](change-of-group/action-of-the-quotient-on-the-cohomology-of-a-normal-subgroup.md),
  for the action of $G/H$ on $H^n(H, A)$
- [The transgression](change-of-group/transgression.md), for $\operatorname{tg}$ in degree one, which the proof
  extends to degree $n$
- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  the cohomology groups

## Proof depends on

- [The transgression](change-of-group/transgression.md), for the cochain description of the transgression
  (Proposition (1.6.6)) used in the proof
- [The action of the quotient on the cohomology of a normal subgroup](change-of-group/action-of-the-quotient-on-the-cohomology-of-a-normal-subgroup.md),
  for $H^1(G, A)^G = H^1(G, A)$, so that restriction lands in the $G/H$-invariants
- [Functoriality and the connecting homomorphisms](change-of-group/functoriality-and-connecting-homomorphisms.md),
  [the long exact cohomology sequence](long-exact-cohomology-sequence.md) and
  [Induced modules are acyclic](induced-modules-are-acyclic.md), for the induction on $n$ by dimension shifting
  along $0 \to A \to \operatorname{Ind}_G(A) \to A_1 \to 0$, which defines $\operatorname{tg}$ in degree $n$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §6, Proposition (1.6.7) (Five Term
  Exact Sequence), p. 67.
