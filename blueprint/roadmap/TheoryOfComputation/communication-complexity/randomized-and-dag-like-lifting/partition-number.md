# Partition number and unambiguous certificate complexity

For $F : X \times Y \to \{0, 1\}$, the **partition number** $\chi(F)$ is the least number of pairwise disjoint monochromatic combinatorial rectangles whose union is $X \times Y$. The **unambiguous certificate complexity** $\mathrm{UC}(f)$ of a query function $f : \{0,1\}^n \to \{0,1\}$ is the least $c$ such that $\{0,1\}^n$ is partitioned into subcubes of codimension at most $c$ on each of which $f$ is constant. Always $\log \chi(F) \le D^{cc}(F) \le O(\log^2 \chi(F))$ (Aho-Ullman-Yannakakis), and lifting a partition by subcubes with a gadget yields a rectangle partition of $f \circ g^n$ of size $2^{O(\mathrm{UC}(f) \log |\mathcal{X}|)}$.

## Depends on

- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)
- [Certificate complexity, degree and decision-tree depth](../query-and-communication-measures/certificate-complexity-degree-and-decision-tree.md)

## Sources

- A. V. Aho, J. D. Ullman, M. Yannakakis, "On notions of information transfer in VLSI circuits", STOC (1983).
- M. Göös, T. Pitassi, T. Watson, "Deterministic communication vs. partition number", FOCS (2015); SIAM Journal on Computing 47 (2018).
