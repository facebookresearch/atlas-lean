# Satisfaction probability at a randomized assignment is the multilinear expansion

Let $\psi : \{-1,1\}^r \to \{0,1\}$ be a predicate with Fourier expansion $\psi(x) = \sum_{S \subseteq [r]} \hat\psi(S) \prod_{i\in S} x_i$, and let $X_1,\dots,X_r$ be independent random signs with means $\mu_1,\dots,\mu_r \in [-1,1]$. Then $\Pr[\psi(X_1,\dots,X_r) = 1] = \sum_S \hat\psi(S) \prod_{i \in S}\mu_i$, the multilinear extension of $\psi$ at $(\mu_1,\dots,\mu_r)$. Hence, for an instance whose constraint scopes consist of distinct variables and a randomized assignment with independent coordinates, the expected fraction of satisfied constraints is the average of these multilinear expressions over the constraints; with repeated variables in a scope the coordinates are not independent and the formula fails.

## Proof sketch

Expand $\psi$ in the Fourier basis and use independence: $\mathbb{E}\prod_{i \in S} X_i = \prod_{i\in S}\mu_i$.

## Depends on

- [Maximum constraint satisfaction problems](maximum-constraint-satisfaction-problems.md)
- [The multilinear extension agrees with its function on the cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/eval-multilinear-extension.md)

## Sources

- R. O'Donnell, Analysis of Boolean Functions, Cambridge University Press, 2014, Exercise 7.20 (randomized assignments).
