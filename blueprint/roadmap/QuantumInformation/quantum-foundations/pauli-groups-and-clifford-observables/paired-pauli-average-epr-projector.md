# Paired Pauli averages give the EPR projector

Let $\Phi$ be the maximally entangled state on two $n$-qubit registers. Then

$$
\mathbb{E}_{a,b\in\{0,1\}^n}\,X^aZ^b\otimes X^aZ^b = |\Phi\rangle\langle\Phi| ,
$$

and for every state $\varphi$ on $M_{2^n}(\mathbb{C})\otimes M_{2^n}(\mathbb{C})$ the weight outside the EPR projection is controlled by agreement of the two ideal Pauli families:

$$
\big\||\Phi\rangle\langle\Phi|-I\big\|_\varphi^2\le\tfrac12\Big(\mathbb{E}_a\|X^a\otimes I-I\otimes X^a\|_\varphi^2+\mathbb{E}_b\|Z^b\otimes I-I\otimes Z^b\|_\varphi^2\Big).
$$

## Proof sketch

In the product basis, averaging the phases $(-1)^{b\cdot(z+z')}$ over $b$ removes the terms with unequal strings on the two registers, and averaging the shifts over $a$ makes all surviving diagonal amplitudes equal, which is $|\Phi\rangle\langle\Phi|$. For the bound, $I-|\Phi\rangle\langle\Phi|$ is a projection, its squared state norm is its expectation, and $I - X^a\otimes X^a = \tfrac12(X^a\otimes I-I\otimes X^a)^2$ for real involutions; averaging over $a$ and $b$ and using $X^aZ^b\otimes X^aZ^b = (X^a\otimes X^a)(Z^b\otimes Z^b)$ yields the inequality.

## Depends on

- [Pauli strings and the Pauli group modulo $i$ as a Heisenberg group](pauli-group-modulo-i.md)
- [States on star-ordered algebras, state-dependent norm and approximation](../states-and-measurements-on-operator-algebras/algebraic-states-and-state-dependent-norm.md)
- [Bell basis and maximally entangled states](../bell-basis-and-maximally-entangled-states.md)

## Proof depends on

- [Local correlations on the maximally entangled state and the transpose trick](maximally-entangled-correlations-transpose-trick.md)

## Sources

- A. Natarajan and T. Vidick, "A quantum linearity test for robustly verifying entanglement", Proceedings of the 49th Annual ACM Symposium on Theory of Computing (STOC 2017), 1003-1015, 2017.
