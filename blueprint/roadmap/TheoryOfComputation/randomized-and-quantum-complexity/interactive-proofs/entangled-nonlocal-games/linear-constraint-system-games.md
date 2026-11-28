# Linear constraint system games and operator solutions

A *binary linear system* is a finite set of equations $\sum_{v \in S_j} x_v = b_j$ over $\mathbb{F}_2$, $j = 1, \dots, m$. Its *game* asks Alice an equation $j$ (she answers an assignment to the variables of $S_j$ satisfying it) and Bob a variable $v$ (he answers a bit), and accepts iff Bob's bit equals Alice's value for $v$; question pairs are drawn from a distribution supported on pairs with $v \in S_j$. The distribution has *full support* if it gives positive probability to every pair $(j, v)$ with $v \in S_j$; the game of Cleve, Liu and Slofstra (Definition 2) asks every such pair. An *operator solution* is an assignment of self-adjoint unitaries $X_v$ (so $X_v^2 = 1$) on a Hilbert space such that $X_u X_v = X_v X_u$ whenever $u, v$ occur in a common equation and $\prod_{v \in S_j} X_v = (-1)^{b_j}$ for every $j$.

## Depends on

- [Entangled strategies and the entangled value of a game](entangled-strategies-and-entangled-value.md)

## Sources

- R. Cleve and R. Mittal, "Characterization of Binary Constraint System Games", ICALP 2014.
- R. Cleve, L. Liu and W. Slofstra, "Perfect Commuting-Operator Strategies for Linear System Games", Journal of Mathematical Physics 58(1), 2017; arXiv:1606.02278, Definition 2.
