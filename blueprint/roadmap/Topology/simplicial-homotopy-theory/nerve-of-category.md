# Nerve of a category

Regard each linearly ordered set $[n] = \{0 < 1 < \dots < n\}$ as a category with exactly one morphism $j \to k$ when $j \le k$ and none otherwise; an order-preserving map $[m] \to [n]$ is then the same as a functor. Let $\mathcal{C}$ be a category. Its *nerve* $N(\mathcal{C})$ is the simplicial set whose set of $n$-simplices $N(\mathcal{C})_n$ is the set of functors $[n] \to \mathcal{C}$, on which a morphism $\alpha\colon [m] \to [n]$ of the simplex category acts by precomposition, $\sigma \mapsto \sigma \circ \alpha$. The category $\mathcal{C}$ need not be small in a previously fixed universe. If its objects have universe level $u$ and its hom-sets have level $v$, its nerve takes values in sets of level $\max(u, v)$; in particular it lies in the original universe when $\mathcal{C}$ is small there.

## Sources

- Jacob Lurie, Higher Topos Theory, Annals of Mathematics Studies 170, Princeton University Press, 2009.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the universe level of the nerve: `CategoryTheory.nerve`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicTopology/SimplicialSet/Nerve.lean#L37-L40.
