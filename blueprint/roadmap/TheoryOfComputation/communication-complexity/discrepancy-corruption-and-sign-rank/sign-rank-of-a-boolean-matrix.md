# Sign-rank of a Boolean matrix

A real matrix $M \in \mathbb{R}^{X \times Y}$ *sign-represents* $f : X \times Y \to \{0,1\}$ if every entry is nonzero and $\mathrm{sign}(M_{xy}) = (-1)^{f(x,y)}$. The *sign-rank* $\mathrm{rk}_\pm(f)$ is the least rank of a sign-representing matrix. It is invariant under negating $f$ and transposing, does not increase on submatrices, is at most the rank of the sign matrix, and an optimal representation can be taken with integer entries.

## Depends on

- [Communication matrix](../deterministic-communication-protocols/comm-matrix.md)

## Sources

- R. Paturi and J. Simon, "Probabilistic Communication Complexity", Journal of Computer and System Sciences 33(1), 1986.
- N. Alon, S. Moran and A. Yehudayoff, "Sign Rank versus VC Dimension", COLT 2016.
