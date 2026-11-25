# Weighted independent domination on chordal graphs is NP-complete

Statement: the decision problem WEIGHTED INDEPENDENT DOMINATING SET for chordal graphs, with natural-number vertex weights and bound in binary, belongs to NP, and every decision problem $L$ in NP is polynomial-time many-one reducible to it: there is a function $f$ from bitstrings to bitstrings, computable in polynomial time, such that $x \in L$ exactly when $f(x)$ is accepted, for every bitstring $x$.

An instance consists of a chordal graph $G = (V, E)$ (every cycle of length at least $4$ has a chord), a weight $w(v) \in \mathbb{Z}_{\ge 0}$ for each vertex, and a bound $B \in \mathbb{Z}_{\ge 0}$; the question is whether there is an independent dominating set $D \subseteq V$ with $\sum_{v \in D} w(v) \le B$.

## Sources

- G. J. Chang, "The weighted independent domination problem is NP-complete for chordal graphs", *Discrete Applied Mathematics* 143 (2004), 351–352, <https://doi.org/10.1016/j.dam.2003.05.004>.
- D. S. Johnson, "The NP-completeness column: an ongoing guide" (tenth edition), *Journal of Algorithms* 5 (1984), 147–160, <https://doi.org/10.1016/0196-6774(84)90045-2>.
- K. Khoshkhah, M. Khosravian Ghadikolaei, J. Monnot and F. Sikora, "Weighted upper edge cover: complexity and approximability", *Journal of Graph Algorithms and Applications* 24 (2020), <https://doi.org/10.7155/jgaa.00519>.
