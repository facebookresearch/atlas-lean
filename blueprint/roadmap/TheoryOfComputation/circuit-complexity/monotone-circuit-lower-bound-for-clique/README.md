# Monotone circuit lower bound for clique

A monotone circuit uses only and and or gates. Razborov's *approximation method* (1985) gave the first superpolynomial lower bound for an explicit monotone function, the clique function: every gate is replaced by an approximator from a small family of monotone functions, the [Erdős–Rado sunflower lemma](../../../Combinatorics/extremal-set-theory/intersecting-families/sunflower-lemma/exists-is-delta-system.md) keeps each replacement cheap, and the approximators are shown to err on many test graphs (cliques and complete multipartite graphs). Alon and Boppana sharpened the method to an exponential bound. Clique is NP-complete, so a superpolynomial bound for general circuits would separate P from NP; the [natural proofs barrier](../../hierarchy-theorems-and-barriers/natural-proofs-barrier/README.md) is one obstacle to extending lower-bound methods to general circuits.

- [The clique function on adjacency-matrix bits](clique-holds.md)
- [The clique function CLIQUE(n, s) on adjacency-matrix bits](clique-of-size.md)
- [Razborov: monotone circuits for clique need superpolynomial size](razborov-monotone-clique.md)
- [Alon–Boppana: monotone circuits for clique need exponential size](alon-boppana-monotone-clique.md)
