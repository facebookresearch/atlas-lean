# Dualizing modules and the abstract duality theorems

This node is still to be broken down. It covers dualizing modules, trace maps and the abstract duality theorems for
profinite groups of finite [cohomological dimension](cohomological-dimension.md), and duality relative to a class
formation, from which local and global Tate duality are derived. For a profinite group $G$ and a discrete
$G$-module $A$, let $D_i(A) = \varinjlim_U H^i(U, A)^*$, over the open normal subgroups $U$ and the duals of the
corestrictions, where $X^*$ is the Pontryagin dual of a discrete torsion group $X$.

## Expansion

This node is still to be broken down. A good expansion states and links:

- for finite strict cohomological dimension, the dualizing module and the duality theorem: if
  $n = \operatorname{scd} G < \infty$, the canonical map $H^n(G, A)^* \to \operatorname{Hom}_G(A, D_n(\mathbb{Z}))$ is an
  isomorphism for every discrete module $A$, and $D = D_n(\mathbb{Z})$ is the dualizing module of $G$, which is also
  that of every open subgroup (Theorem (3.4.1) and the remark after it); Corollary (3.4.2); and the duality theorem
  (3.4.3): if moreover $D_k(\mathbb{Z}) = 0$ for $k < n$, then for $A$ finitely generated over $\mathbb{Z}$ whose
  $\ell$-primary part is nontrivial only for primes $\ell$ such that $D$ is $\ell$-divisible, cup product and the
  trace map $\operatorname{tr} \colon H^n(G, D) \to \mathbb{Q}/\mathbb{Z}$ give
  $H^i(G, \operatorname{Hom}(A, D)) \cong H^{n-i}(G, A)^*$ for all $i$, with Remark 1 after (3.4.3) on replacing the
  trace by any isomorphism $H^n(G, D) \cong \mathbb{Q}/\mathbb{Z}$;
- for a nonempty set $P$ of primes with $\operatorname{cd}_P G = n < \infty$, the dualizing module $D_P = D_n(\mathbb{Z}_P)$
  of the $P$-torsion modules, which is also that of every open subgroup (Theorem (3.4.4) and the remark after
  (3.4.1)); Serre's criterion relating $\operatorname{scd}_p G$ to $D_{(p)}$ (Corollary (3.4.5)); and the duality
  theorem for finite modules (3.4.6): $D_i(\mathbb{Z}/p\mathbb{Z}) = 0$ for $p \in P$ and $i < n$ if and only if cup
  product and the trace give $H^i(G, \operatorname{Hom}(A, D_P)) \cong H^{n-i}(G, A)^*$ for all $i$ and all finite
  $P$-torsion modules $A$;
- duality relative to a class formation: the Tate–Nakayama theorem (Milne, *Arithmetic Duality Theorems*,
  Theorem I.0.2), the reciprocity map of a class formation (Theorem I.1.3) and the duality theorem for a class
  formation (Theorem I.1.8); and the duality theorem for a level-compact formation module $C$ with divisible
  universal norm groups $N_U C$ (Neukirch–Schmidt–Wingberg (3.1.11)), stated with the
  [Tate cohomology of profinite groups](discrete-coefficients/tate-cohomology-of-profinite-groups.md) and
  [level-compact modules](discrete-coefficients/level-compact-modules.md).

## Depends on

- [Cohomological dimension of a profinite group](cohomological-dimension.md), for $\operatorname{scd} G$ and
  $\operatorname{cd}_P G$
- [Cup products for profinite groups](discrete-coefficients/cup-products.md), for the duality pairings
- [Inflation, restriction and corestriction for profinite groups](discrete-coefficients/inflation-restriction-and-corestriction.md),
  for the corestrictions in $D_i(A)$
- [Tate cohomology of profinite groups](discrete-coefficients/tate-cohomology-of-profinite-groups.md), for the
  duality of class formations
- [Level-compact modules](discrete-coefficients/level-compact-modules.md), for the formation modules of (3.1.11)

## Proof depends on

- [Restriction, corestriction, inflation and Tate's theorem in group cohomology](../restriction-corestriction-inflation-and-tate-s-theorem.md),
  for the finite-group results, Tate's theorem among them, from which the profinite statements pass to the limit
- [Shapiro's lemma for profinite groups](discrete-coefficients/shapiro-s-lemma.md), used in the proofs of (3.4.1)
  and (3.4.6)
- [Properties of cohomological dimension](properties-of-cohomological-dimension.md), for (3.3.4) and (3.3.5) in
  these proofs; the proof of (3.4.1) also uses Proposition (3.3.11), as Neukirch–Schmidt–Wingberg cite it there,
  which an expansion of this node states

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter III, §4, the modules $D_i(A)$ and
  Theorem (3.4.1) with the remark after it, pp. 181–182; Corollary (3.4.2) and Duality Theorem (3.4.3),
  p. 183, with Remark 1 after it, p. 184; Theorem (3.4.4) and Corollary (3.4.5), p. 185; Duality Theorem (3.4.6),
  p. 186; Chapter III, §1, Duality Theorem (3.1.11), p. 160.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, §0, Theorem 0.2 (Tate–Nakayama), and §1, Theorems 1.3 and 1.8.
