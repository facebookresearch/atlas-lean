# Power set of a subset of a fixed set

Let $U$ be a set and let $A \subseteq U$. The *power set* of $A$ within $U$ is the family $\mathcal{P}(A) = \{s \subseteq U : s \subseteq A\}$ of all subsets of $U$ that are contained in $A$: a subset $s$ of $U$ belongs to $\mathcal{P}(A)$ if and only if $s \subseteq A$. The family is formed inside the fixed ambient set $U$; the existence of a power set for every set, which is the power set axiom of Zermelo–Fraenkel set theory, is not part of this definition.

## Sources

- Herbert B. Enderton, Elements of Set Theory, Academic Press, 1977.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the power set of a subset of a fixed type as the family of all subsets of the type contained in it: `Set.powerset`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Set/Defs.lean#L257.
