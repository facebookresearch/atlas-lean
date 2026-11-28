# Level-compact modules

Let $G$ be a profinite group. A level-compact $G$-module is a discrete $G$-module $A$ together with, for each open
subgroup $U \subseteq G$, a compact group topology on $A^U$, such that for all open subgroups $U$ and $V$ and all
$\sigma \in G$ with $V \subseteq \sigma U \sigma^{-1}$ the map

$$
\sigma \colon A^U \longrightarrow A^V, \qquad a \longmapsto \sigma a,
$$

is continuous. In particular, for $V \subseteq U$ the group $A^U$ carries the subgroup topology of $A^V$, and the
norm map $N_{U/V} \colon A^V \to A^U$ is continuous.

## Depends on

- [Continuous Module](../../../not-yet-classified/discrete-gmodules/continuous-module.md), for the discrete
  $G$-modules

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §9, Definition (1.9.10) and the
  remark after it, p. 91.
