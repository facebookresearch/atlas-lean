# Universal trees

The trees considered here are rooted, have all leaves at the same depth, and order the children of each node: a tree of
height $0$ is a leaf, and a tree of height $h + 1$ is a finite list $[t_1, \dots, t_k]$ of trees of height $h$. The *size* of a tree is
its number of leaves. A tree $t$ *embeds* into a tree $T$ if both are leaves, or $t = [t_1, \dots, t_k]$, $T = [T_1, \dots, T_{k'}]$ and
there are indices $i_1 < \dots < i_k$ such that each $t_j$ embeds into $T_{i_j}$. A tree is *$(n, h)$-universal* if every tree of size
$n$ and height $h$ embeds into it. The complete tree of height $h$ in which every node has $n$ children is $(n, h)$-universal and has
size $n^h$.

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Section 2.5, the definitions of trees and embeddings and Definition 2.2.
- W. Czerwiński, L. Daviaud, N. Fijalkow, M. Jurdziński, R. Lazić and P. Parys, "Universal trees grow inside separating automata: quasi-polynomial lower bounds for parity games", *Proceedings of the 30th ACM-SIAM SODA*, 2019, arXiv:1807.10546v2: Section 2 (ordered trees and universal trees).
