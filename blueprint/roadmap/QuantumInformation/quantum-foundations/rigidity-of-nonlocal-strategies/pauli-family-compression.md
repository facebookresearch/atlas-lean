# Compression of the Pauli family to exact Pauli strings

Let $X(a),Z(b)$, $a,b\in\{0,1\}^n$, be unitaries on $\mathbb{C}^\kappa$ with Pauli family $f(s,a,b) = (-1)^sX(a)Z(b)$. There are a finite set $J$ and a single isometry $W:\mathbb{C}^\kappa\to\mathbb{C}^{2^n}\otimes\mathbb{C}^J$, not depending on any state, such that for every state $\varphi$ on $M_\kappa(\mathbb{C})$

$$
\mathbb{E}_{a,b}\big\|X(a)Z(b)-W^*\big(X^aZ^b\otimes I_J\big)W\big\|_\varphi^2\le\mathbb{E}_{p,q}\|f(p)f(q)-f(pq)\|_\varphi^2 .
$$

The bound does not depend on $n$; combined with the Pauli-family defect bound it controls the distance to exact Pauli strings by the consistency, anticommutation and linearity defects of a strategy.

## Proof sketch

Apply compression of the regular representation to the Pauli family. The averaging isometry lands in the $-1$ eigenspace of the image of the central element, where the regular representation is a representation of the Pauli group in which $-1$ acts as $-1$. By the Stone-von Neumann theorem for the Pauli relations this representation is unitarily equivalent to $X^aZ^b\otimes I_J$, which defines $W$.

## Depends on

- [Pauli strings and the Pauli group modulo $i$ as a Heisenberg group](../pauli-groups-and-clifford-observables/pauli-group-modulo-i.md)
- [States on star-ordered algebras, state-dependent norm and approximation](../states-and-measurements-on-operator-algebras/algebraic-states-and-state-dependent-norm.md)

## Proof depends on

- [Compression of the regular representation (first step of Gowers-Hatami stability)](regular-representation-compression.md)
- [Stone-von Neumann theorem for the Pauli relations](../pauli-groups-and-clifford-observables/pauli-stone-von-neumann.md)
- [Pauli-family defect from consistency, anticommutation and linearity](pauli-family-defect-bound.md)

## Sources

- A. Natarajan and T. Vidick, "A quantum linearity test for robustly verifying entanglement", Proceedings of the 49th Annual ACM Symposium on Theory of Computing (STOC 2017), 1003-1015, 2017.
- W. T. Gowers and O. Hatami, "Inverse and stability theorems for approximate representations of finite groups", Sbornik: Mathematics 208:1784-1817, 2017.
