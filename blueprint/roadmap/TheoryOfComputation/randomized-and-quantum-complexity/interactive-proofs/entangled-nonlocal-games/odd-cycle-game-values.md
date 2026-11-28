# Classical and entangled values of the odd-cycle game

For odd $n \ge 3$, in the *odd-cycle game* the referee picks a uniform vertex $x \in \mathbb{Z}_n$ and asks Alice $x$ and Bob either $x$ (requiring equal answers) or $x+1$ (requiring different answers), each with probability $1/2$. Its classical value is $1 - \frac{1}{2n}$, and its entangled value is $\cos^2\big(\frac{\pi}{4n}\big)$, attained by measuring a maximally entangled qubit pair in bases rotated by angles proportional to $x \pi/(2n)$.

## Proof sketch

Classically an odd cycle has no proper 2-colouring, so at least one of the $2n$ constraints fails. Quantumly it is an XOR game; Tsirelson's characterization reduces the value to choosing unit vectors in the plane, and equally spaced angles are optimal.

## Depends on

- [XOR games and Tsirelson's vector characterization](xor-games-and-tsirelsons-theorem.md)

## Sources

- R. Cleve, P. Høyer, B. Toner and J. Watrous, "Consequences and Limits of Nonlocal Strategies", IEEE Conference on Computational Complexity, 2004.
