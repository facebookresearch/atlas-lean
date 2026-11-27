# Correctness and step count of Kosaraju's SCC algorithm

Throughout, a directed graph $G$ on a finite vertex type $V$, with decidable equality, a Boolean equality test that agrees with it and a hash function on vertices (used by the traversals and the transpose), is given by a duplicate-free list $v_1, \dots, v_{|V|}$ of all vertices and, for each vertex $v$, an ordered adjacency list $\mathrm{adj}_G(v)$ of out-neighbors (entries may repeat). The transpose $G^{T}$ has the same vertex list, and $\mathrm{adj}_{G^T}(v)$ lists, once each and in vertex-list order, the vertices $u$ with $v \in \mathrm{adj}_G(u)$. Kosaraju's algorithm runs a left-first depth-first search of $G$ with roots $v_1, \dots, v_{|V|}$ in that order, lists the vertices in decreasing order of finishing time, runs a depth-first search of $G^T$ with roots taken in that order, and cuts the preorder of this second search at its forest roots; the resulting lists are the Kosaraju blocks.

The following holds for every such graph $G$, with $V$ the number of vertices, $E = \sum_{v} \lvert \mathrm{adj}_G(v) \rvert$ and $E_2 = \sum_{v} \lvert \mathrm{adj}_{G^T}(v) \rvert$.

1. The Kosaraju blocks form the strongly connected component partition of $G$: every block is nonempty and duplicate-free, distinct blocks are disjoint, the blocks cover exactly the vertices of $G$, two vertices share a block exactly when each is reachable from the other, and for every vertex $m$ of a block $B$, a vertex $v$ is strongly connected to $m$ exactly when $v \in B$.
2. The first search, run as the step-by-step depth-first-search machine from its initial state with roots $v_1, \dots, v_{|V|}$, halts with an empty work stack and outputs the whole-graph search after exactly

    $$n_1 = 2V + E$$

    steps.
3. The second search, run the same way on $G^T$ with roots in decreasing finishing order, halts with an empty work stack and outputs that search after exactly

    $$n_2 = R + P + \sum_{v \in \mathrm{pre}} \lvert \mathrm{adj}_{G^T}(v) \rvert$$

    steps, where $R$ is the length of the root list (the decreasing finishing order), $\mathrm{pre}$ is the preorder of the second search and $P$ its length.
4. In total,

    $$n_1 + n_2 \le 4V + 2(E + E_2).$$

These are counts of transitions of the specified depth-first-search machine only; the cost of evaluating adjacency lists is not counted.

## Sources

- M. Sharir, "A strong-connectivity algorithm and its applications in data flow analysis", *Computers & Mathematics with Applications* 7 (1981), 67-72.
- A. V. Aho, J. E. Hopcroft, and J. D. Ullman, *The Design and Analysis of Computer Algorithms*, Addison-Wesley, 1974, Section 5.5: background on strongly connected components, by a different (lowlink) method.
