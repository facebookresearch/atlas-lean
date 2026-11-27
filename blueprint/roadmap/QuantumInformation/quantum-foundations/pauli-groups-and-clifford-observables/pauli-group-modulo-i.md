# Pauli strings and the Pauli group modulo $i$ as a Heisenberg group

On $n$ qubits with computational basis $\{0,1\}^n$, the *Pauli strings* are $X^a|z\rangle = |z+a\rangle$ and $Z^b|z\rangle = (-1)^{b\cdot z}|z\rangle$ for $a,b\in\{0,1\}^n$, and their products $X^aZ^b$; these are real unitary matrices with $Z^bX^a = (-1)^{a\cdot b}X^aZ^b$. The *Pauli group modulo $i$* is the set of triples $(s,a,b)\in\mathbb{F}_2\times\mathbb{F}_2^n\times\mathbb{F}_2^n$, standing for $(-1)^sX^aZ^b$, with multiplication

$$
(s,a,b)\cdot(s',a',b') = (s+s'+b\cdot a',\ a+a',\ b+b'),
$$

a central extension of $\mathbb{F}_2^{2n}$ by $\mathbb{F}_2$ with bilinear cocycle $b\cdot a'$ (a finite Heisenberg group of order $2^{2n+1}$). The central element $-1 = (1,0,0)$ squares to the identity.

## Depends on

- [Pauli operator $X^a Z^b$ on $n$ qubits](../../quantum-error-correction/css-codes/pauli.md)
- [The Pauli group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-on-n-qubits.md)

## Sources

- A. Natarajan and T. Vidick, "A quantum linearity test for robustly verifying entanglement", Proceedings of the 49th Annual ACM Symposium on Theory of Computing (STOC 2017), 1003-1015, 2017.
- M. A. Nielsen and I. L. Chuang, "Quantum Computation and Quantum Information: 10th Anniversary Edition", Cambridge University Press, 2010.
