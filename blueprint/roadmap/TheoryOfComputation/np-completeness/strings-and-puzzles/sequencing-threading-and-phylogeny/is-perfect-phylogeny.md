# Perfect phylogenies

A triple $(T, f, \mathrm{lab})$ is a perfect phylogeny for a PERFECT PHYLOGENY instance when $T$ is a tree on the nodes $0, \dots, N - 1$; species $s$ sits at node $f(s)$ and keeps its states there, $\mathrm{lab}(f(s), c)$ being the state of $s$ for character $c$; every node carries, for each character, a state that some species has; and for each character $c$ and state $x$, the nodes $v$ with $\mathrm{lab}(v, c) = x$ induce a connected subgraph of $T$ whenever there is such a node (an empty set of nodes is allowed).
