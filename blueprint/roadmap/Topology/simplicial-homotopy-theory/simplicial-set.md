# Simplicial set

Let $\Delta$ be the *simplex category*: its objects are the linearly ordered sets $[n] = \{0 < 1 < \dots < n\}$ for integers $n \ge 0$, and its morphisms $[m] \to [n]$ are the order-preserving (non-decreasing) maps. Fix a universe of sets, and let $\mathrm{Set}$ be the category whose objects are the sets in that universe and whose morphisms are functions. A *simplicial set* is a functor $K\colon \Delta^{\mathrm{op}} \to \mathrm{Set}$. Its $n$-simplices are the elements of $K_n = K([n])$, and a morphism $\alpha\colon [m] \to [n]$ of $\Delta$ induces a map $\alpha^*\colon K_n \to K_m$. A *map of simplicial sets* $K \to L$ is a natural transformation between these functors.

## Sources

- Jacob Lurie, Higher Topos Theory, Annals of Mathematics Studies 170, Princeton University Press, 2009.
