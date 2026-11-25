# For ordinals, inclusion is membership or equality

Work in Zermelo–Fraenkel set theory, where every member of a set is itself a set. An *ordinal* is a transitive set every member of which is also a transitive set; by the axiom of foundation, these are exactly the transitive sets that are well-ordered by membership. Let $\alpha$ and $\beta$ be ordinals. Then $\alpha \subseteq \beta$ holds if and only if $\alpha \in \beta$ or $\alpha = \beta$. In particular, if $\alpha \subsetneq \beta$, then $\alpha \in \beta$.

## Sources

- Herbert B. Enderton, Elements of Set Theory, Academic Press, 1977.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for ordinals as transitive sets all of whose members are transitive: `ZFSet.IsOrdinal`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/SetTheory/ZFC/Ordinal.lean#L111-L115.
