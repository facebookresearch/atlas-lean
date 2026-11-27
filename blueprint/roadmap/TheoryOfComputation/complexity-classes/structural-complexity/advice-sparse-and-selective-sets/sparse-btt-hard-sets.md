# Ogiwara–Watanabe: sparse sets hard for NP under bounded truth-table reductions

If $\mathrm{SAT}$ reduces to a sparse set by a polynomial-time bounded truth-table reduction (a constant number of non-adaptive queries), then $\mathsf{P}=\mathsf{NP}$. The same conclusion holds for polynomial-time conjunctive truth-table reductions to sparse sets, and more generally if $\mathrm{SAT}$ btt-reduces to a set having a conjunctive reduction to a sparse set.

## Proof sketch

Use the left set of SAT (partial assignments lexicographically left of the largest satisfying assignment) and a Hausdorff decomposition of the btt reduction into Boolean combinations of conjunctive pieces; a search that keeps at most $\mathrm{poly}$ many nodes per level, the last node of each run whose queries lie in a small set, preserves the largest satisfiable node.

## Depends on

- [Sparse decision problems](../../mahaney-s-theorem/sparse.md)
- [The complexity class NP](../../the-classes-p-np-and-conp/np.md)
- [The complexity class P](../../the-classes-p-np-and-conp/p.md)
- [Polynomial-time truth-table, bounded and Turing reductions](../reducibilities-and-isomorphism/truth-table-reductions.md)

## Proof depends on

- [Cook–Levin theorem: SAT is NP-complete](../../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)
- [Mahaney's theorem: sparse NP-complete sets imply P = NP](../../mahaney-s-theorem/mahaney.md)

## Sources

- Vikraman Arvind, Johannes Köbler and Martin Mundhenk, "On Bounded Truth-Table, Conjunctive, and Randomized Reductions to Sparse Sets", 12th Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 1992), Lecture Notes in Computer Science 652, 1992.
- Mitsunori Ogiwara and Osamu Watanabe, "On Polynomial-Time Bounded Truth-Table Reducibility of NP Sets to Sparse Sets", SIAM Journal on Computing 20(3), 1991.
