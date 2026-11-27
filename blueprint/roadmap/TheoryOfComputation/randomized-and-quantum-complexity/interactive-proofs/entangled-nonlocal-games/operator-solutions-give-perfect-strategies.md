# Cleve–Mittal: finite-dimensional operator solutions give perfect strategies

If a binary linear system has an operator solution $(X_v)$ in $M_d(\mathbb{C})$ for some finite $d \ge 1$, then its game has a perfect entangled strategy: on the maximally entangled state of $\mathbb{C}^d \otimes \mathbb{C}^d$, Alice measures the commuting observables $\{X_v : v \in S_j\}$ jointly and Bob measures $X_v^{\mathsf T}$, and they win with probability $1$ for every question distribution supported on incident pairs. Conversely (Cleve–Liu–Slofstra), a perfect commuting-operator strategy yields an operator solution in the GNS representation of the state.

## Proof sketch

On the maximally entangled state $(M \otimes 1)\psi = (1 \otimes M^{\mathsf T})\psi$, so Bob's outcome for $X_v^{\mathsf T}$ always equals Alice's outcome for $X_v$. Alice's joint outcomes satisfy the equation because the product of the commuting observables is $(-1)^{b_j}$.

## Depends on

- [Linear constraint system games and operator solutions](linear-constraint-system-games.md)
- [Commuting-operator strategies and value](commuting-operator-strategies-and-value.md)

## Sources

- R. Cleve and R. Mittal, "Characterization of Binary Constraint System Games", ICALP 2014.
- R. Cleve, L. Liu and W. Slofstra, "Perfect Commuting-Operator Strategies for Linear System Games", Journal of Mathematical Physics 58(1), 2017.
