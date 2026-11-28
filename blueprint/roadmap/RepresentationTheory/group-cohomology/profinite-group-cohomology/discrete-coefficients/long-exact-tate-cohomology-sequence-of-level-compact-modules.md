# The long exact Tate cohomology sequence of level-compact modules

Let $G$ be a profinite group. For a [level-compact](level-compact-modules.md) $G$-module $A$ and an open normal
subgroup $U$, let $N_U A = \bigcap_{V} N_{U/V} A^V$, over the open normal subgroups $V \subseteq U$ of $G$, be the
group of universal norms of $U$. Let

$$
0 \longrightarrow A' \xrightarrow{\ i\ } A \xrightarrow{\ j\ } A''
$$

be an exact sequence of level-compact $G$-modules such that the induced map $N_U A \to N_U A''$ is surjective for a
cofinal system of open normal subgroups $U$ of $G$ (and hence for all of them). Then there is a long exact
sequence of [Tate cohomology](tate-cohomology-of-profinite-groups.md) groups

$$
\cdots \to \hat H^{-n}(G, A') \to \hat H^{-n}(G, A) \to \hat H^{-n}(G, A'') \to \cdots
\to \hat H^0(G, A') \to \hat H^0(G, A) \to \hat H^0(G, A''),
$$

and if $j$ is surjective, a long exact cohomology sequence unbounded in both directions, from $-\infty$ to
$+\infty$.

## Depends on

- [Level-compact modules](level-compact-modules.md), for level-compact modules and the topologies on $A^U$
- [Tate cohomology of profinite groups](tate-cohomology-of-profinite-groups.md), for $\hat H^i(G, -)$

## Proof depends on

- [Tate cohomology of profinite groups](tate-cohomology-of-profinite-groups.md), for Lemmas (1.9.11) and
  (1.9.12), used to pass to the inverse limit over $U$
- [The long exact Tate cohomology sequence of a finite group](long-exact-tate-cohomology-sequence-of-a-finite-group.md),
  for the exact sequences of the finite groups $G/U$, which are exact sequences of compact groups

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §9, Proposition (1.9.13) and the
  beginning of its proof, pp. 93–94.
