# 2-RAINBOW DOMINATION is NP-complete

The 2-RAINBOW DOMINATION decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a finite simple undirected graph `G = (V, E)` and a non-negative integer `K`. Question: is there a 2-rainbow dominating function of weight at most `K`, that is, a function `f : V → 𝒫({1, 2})` such that every vertex `v` with `f(v) = ∅` has neighbors whose labels together cover `{1, 2}`, and `∑_{v ∈ V} |f(v)| ≤ K`?

## Sources

- B. Brešar and T. Kraner Šumenjak, "On the 2-rainbow domination in graphs", Discrete Applied Mathematics 155(17) (2007), 2394-2400, doi:10.1016/j.dam.2007.07.018.
