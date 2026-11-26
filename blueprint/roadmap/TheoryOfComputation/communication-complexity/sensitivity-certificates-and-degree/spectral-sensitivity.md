# Sensitivity graph and spectral sensitivity

The *sensitivity graph* $G_f$ of $f : \{0,1\}^n \to \{0,1\}$ is the subgraph of the hypercube $Q_n$ containing the edges $\{x, x \oplus e_i\}$ with $f(x) \ne f(x \oplus e_i)$. The *spectral sensitivity* $\lambda(f)$ is the spectral norm (largest eigenvalue in absolute value) of the adjacency matrix $A_f$ of $G_f$. Since a vertex of $G_f$ has degree $s(f, x)$, $\lambda(f) \le s(f)$.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Sources

- S. Aaronson, S. Ben-David, R. Kothari, S. Rao and A. Tal, "Degree vs. Approximate Degree and Quantum Implications of Huang's Sensitivity Theorem", STOC 2021.
