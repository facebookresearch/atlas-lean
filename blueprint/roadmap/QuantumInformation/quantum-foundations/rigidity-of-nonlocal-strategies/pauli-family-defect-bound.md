# Pauli-family defect from consistency, anticommutation and linearity

In a star-ordered algebra with state $\varphi$, let $X(a),Z(b),Z^B(b)$, $a,b\in\{0,1\}^n$, be unitaries with each $Z^B(b')$ commuting with every $X(a)$ and $Z(b)$. The *Pauli family* is $f(s,a,b) = (-1)^sX(a)Z(b)$ on the Pauli group modulo $i$. Then, with $p,q$ uniform on that group,

$$
\mathbb{E}_{p,q}\|f(p)f(q)-f(pq)\|_\varphi^2\le5\big(8\varepsilon_c+\varepsilon_a+\varepsilon_X+\varepsilon_Z\big),
$$

where $\varepsilon_c = \mathbb{E}_b\|Z(b)-Z^B(b)\|_\varphi^2$, $\varepsilon_a = \mathbb{E}_{a,b}\|Z(b)X(a)-(-1)^{a\cdot b}X(a)Z(b)\|_\varphi^2$, $\varepsilon_X = \mathbb{E}_{a,a'}\|X(a)X(a')-X(a+a')\|_\varphi^2$ and $\varepsilon_Z = \mathbb{E}_{b,b'}\|Z(b)Z(b')-Z(b+b')\|_\varphi^2$.

## Proof sketch

Pointwise, the defect $X(a)Z(b)X(a')Z(b')-(-1)^{a'\cdot b}X(a+a')Z(b+b')$ is reduced to five terms: two consistency swaps of $Z$ with Bob's commuting copy (each counted twice), one anticommutation defect, and the two linearity defects. Each swap uses that left multiplication by a unitary preserves the state norm. Cauchy-Schwarz $(x_1+\dots+x_5)^2\le5\sum x_i^2$ and averaging over the group give the bound.

## Depends on

- [Pauli strings and the Pauli group modulo $i$ as a Heisenberg group](../pauli-groups-and-clifford-observables/pauli-group-modulo-i.md)
- [States on star-ordered algebras, state-dependent norm and approximation](../states-and-measurements-on-operator-algebras/algebraic-states-and-state-dependent-norm.md)

## Sources

- A. Natarajan and T. Vidick, "A quantum linearity test for robustly verifying entanglement", Proceedings of the 49th Annual ACM Symposium on Theory of Computing (STOC 2017), 1003-1015, 2017.
