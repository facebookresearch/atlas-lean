# The 3SUM, APSP and Orthogonal Vectors hypotheses

The following hypotheses of fine-grained complexity are stated for the word-RAM with $O(\log n)$-bit words, where $n$ is the input size, and each excludes randomized algorithms as well.

- **3SUM.** The 3-SUM problem asks, for a set $S$ of $n$ integers from $\{-n^c, \dots, n^c\}$ with $c$ a constant, whether there are $x, y, z \in S$ with $x + y + z = 0$. The *3-SUM hypothesis* states that 3-SUM on $n$ integers in $\{-n^4, \dots, n^4\}$ cannot be solved in time $O(n^{2 - \varepsilon})$ for any $\varepsilon > 0$.
- **APSP.** The APSP problem asks, for an $n$-node graph with integer edge weights in $\{-M, \dots, M\}$ for some $M = \mathrm{poly}(n)$ and no negative-weight cycle, for the shortest-path distance between every pair of nodes. The *APSP hypothesis* states that for large enough $c$, APSP on $n$-node graphs with edge weights in $\{-n^c, \dots, n^c\}$ and no negative cycles cannot be solved in time $O(n^{3 - \varepsilon})$ for any $\varepsilon > 0$.
- **Orthogonal Vectors.** For a constant $k \ge 2$ and $d = \omega(\log n)$, the $k$-OV problem asks, for sets $A_1, \dots, A_k \subseteq \{0,1\}^d$ of $n$ vectors each, whether there are $a_1 \in A_1, \dots, a_k \in A_k$ with $\sum_{i=1}^{d} \prod_{j=1}^{k} a_j[i] = 0$; OV is the case $k = 2$. The *$k$-OV hypothesis* states that $k$-OV on instances of size $n$ cannot be solved in time $n^{k - \varepsilon} \mathrm{poly}(d)$ for any constant $\varepsilon > 0$.

The 3-SUM and APSP hypotheses are false. Alman and Vassilevska Williams solve 3-SUM on $n$ integers of polynomially bounded magnitude deterministically in time $O(n^{1.9992})$, and APSP on directed $n$-node graphs with polynomially bounded integer weights deterministically in time $O(n^{2.9995})$; by known reductions the real-valued versions of both hypotheses fail as well. Their algorithm does not bear on the Orthogonal Vectors hypothesis, which remains open. Results conditioned on the 3-SUM or APSP hypothesis remain valid as implications.

## Depends on

- [The word-RAM model](the-word-ram-model.md)

## Sources

- V. Vassilevska Williams, "On some fine-grained questions in algorithms and complexity", *Proceedings of the ICM 2018*, <http://people.csail.mit.edu/virgi/eccentri.pdf>, Section 2.1 (Hypotheses 2 and 3 with the 3-SUM and APSP problems) and Section 3 (the OV and $k$-OV problems and Hypothesis 4)
- J. Alman and V. Vassilevska Williams, "Truly subquadratic 3SUM and truly subcubic APSP via triangles in sparse lopsided graphs", arXiv:2610.06783, 2026, abstract
