# Feasible instances of NNI DISTANCE

An instance $(m, T_1, T_2, K)$ is feasible when both tree data $T_1$ and $T_2$ [describe unrooted binary phylogenetic trees](is-phylo-tree.md) on the $m$ taxa, with their supplied leaf lists, and the nni distance between the two trees is at most $K$: some sequence of at most $K$ nni steps, each preserving the leaf of every taxon, turns the first tree into one isomorphic to the second.
