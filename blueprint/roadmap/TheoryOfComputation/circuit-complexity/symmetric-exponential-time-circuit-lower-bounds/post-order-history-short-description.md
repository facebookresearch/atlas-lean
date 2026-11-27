# Li: with post-order traversal the history of Korten's reduction has a description of size poly(n)

Run Korten's reduction with $T=n\cdot 2^{2n+1}$ (tree height $2n+1$) but traverse vertices in **post-order** (left subtree, right subtree, then root). Then the resulting partially assigned GGM tree is the union of $O(n)$ fully assigned GGM subtrees together with vertices marked $\bot$. Hence the whole exponentially long history is determined by the $O(n)$ subtree roots and their values, a description of $\mathrm{poly}(n)$ bits, and the value at any vertex is computable from this description in polynomial time.

## Proof sketch

In post-order, when a vertex $u$ is processed both its subtrees are complete, so every assigned subtree hanging off the current root-to-frontier path is fully assigned and is determined by its root value via the GGM evaluation lemma. The current root-to-frontier path has length $O(n)$, so there are $O(n)$ maximal fully assigned subtrees. Comparing two vertices in post-order takes time linear in the height by locating their lowest common ancestor.

## Depends on

- [Korten's reduction: from a non-image of the GGM tree, an NP oracle finds a non-image of C](korten-reduction-ggm-tree.md)
- [GGM-tree evaluation: every vertex value of the GGM tree GGM_T of C on input x is computable in time Õ(|C| log T)](ggm-tree-vertex-evaluation.md)

## Sources

- Zeyong Li, "Symmetric Exponential Time Requires Near-Maximum Circuit Size: Simplified, Truly Uniform", STOC (2024), arXiv:2310.17762.
