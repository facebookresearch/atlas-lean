# Zielonka tree of a Muller condition

Let $\mathrm{Muller}(\mathcal{F})$ be a [Muller objective](muller-rabin-and-streett-objectives.md) over the set of colors $C$. Its
*Zielonka tree* $T_{\mathcal{F}}$ is the rooted tree whose nodes are labelled by subsets of $C$, built inductively: the root is
labelled $C$, and the children of a node labelled $S$ are labelled by the maximal nonempty subsets $S_1, \dots, S_k$ of $S$ such that
$S_i \in \mathcal{F}$ if and only if $S \notin \mathcal{F}$ (the empty set never occurs as a set of colours seen infinitely often). Several nodes may
carry the same label. The *height* of the tree is the number of nodes on a longest branch.

The number $m_{\mathcal{F}}$ is defined by induction on the tree: $m_{\mathcal{F}} = 1$ if the tree is a single leaf; otherwise, with
$\mathcal{F}_1, \dots, \mathcal{F}_k$ the families induced on the subtrees of the children of the root, $m_{\mathcal{F}}$ is the sum of the
$m_{\mathcal{F}_i}$ if $C \in \mathcal{F}$ and their maximum if $C \notin \mathcal{F}$.

## Depends on

- [Muller, Rabin and Streett objectives](muller-rabin-and-streett-objectives.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 3 (N. Fijalkow and F. Horn, "Regular games"): Definition 3.1 (Zielonka tree) and Definition 3.2 (memory requirements $m_{\mathcal{F}}$).
