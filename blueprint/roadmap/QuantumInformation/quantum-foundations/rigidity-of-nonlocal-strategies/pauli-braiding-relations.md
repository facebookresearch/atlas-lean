# Pauli braiding relations from anticommutation, consistency and linearity

In a star-ordered algebra with state $\varphi$, let $X(a),Z(b)$ be the first player's unitaries and $X'(a),Z'(b)$ the second player's unitaries ($a,b\in\{0,1\}^n$), with $X(a)$ and $Z(b)$ commuting with every $Z'(b')$, $Z(b)$ commuting with every $X'(a')$, and $X(0) = 1$. Then

$$
\mathbb{E}_{a,b}\|Z(b)X(a)-(-1)^{a\cdot b}X(a)Z(b)\|_\varphi^2\le33\,\mathbb{E}_{a,b}\big[\mathbf{1}_{a\cdot b=1}\|X(a)Z(b)+Z(b)X(a)\|_\varphi^2\big]+32\big(\varepsilon_Z+\kappa_Z+\kappa_X\big),
$$

where $\varepsilon_Z = \mathbb{E}_{c,c'}\|Z(c)Z(c')-Z(c+c')\|_\varphi^2$, $\kappa_Z = \mathbb{E}_c\|Z(c)-Z'(c)\|_\varphi^2$ and $\kappa_X = \mathbb{E}_a\|X(a)-X'(a)\|_\varphi^2$. The key transfer step: for contractions with $X$ commuting with $Z'$ and $Z$ commuting with $X'$, and $|s| = 1$, $\|ZX-sXZ\|_\varphi\le2\|X-X'\|_\varphi+2\|Z-Z'\|_\varphi+\|X'Z'-sZ'X'\|_\varphi$.

## Proof sketch

Anticommutation is tested only on pairs with $a\cdot b = 1$. For $a\cdot b = 0$, write $b = c+(c+b)$ with $a\cdot c = 1$ and $a\cdot(c+b) = 1$ for a suitable fraction of $c$; linearity of $Z$ splits $Z(b)$ into $Z(c)Z(c+b)$, each factor anticommutes with $X(a)$ up to a tested defect, and consistency moves factors to the other player to commute them past each other. Averaging over $c$ and Cauchy-Schwarz yield the constants.

## Depends on

- [Pauli strings and the Pauli group modulo $i$ as a Heisenberg group](../pauli-groups-and-clifford-observables/pauli-group-modulo-i.md)
- [States on star-ordered algebras, state-dependent norm and approximation](../states-and-measurements-on-operator-algebras/algebraic-states-and-state-dependent-norm.md)

## Sources

- A. Natarajan and T. Vidick, "A quantum linearity test for robustly verifying entanglement", Proceedings of the 49th Annual ACM Symposium on Theory of Computing (STOC 2017), 1003-1015, 2017.
