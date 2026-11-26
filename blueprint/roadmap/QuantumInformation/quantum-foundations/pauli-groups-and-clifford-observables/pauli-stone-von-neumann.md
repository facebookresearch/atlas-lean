# Stone-von Neumann theorem for the Pauli relations

Let $X(a),Z(b)$, $a,b\in\{0,1\}^n$, be Hermitian matrices on $\mathbb{C}^\kappa$ such that $a\mapsto X(a)$ and $b\mapsto Z(b)$ are representations of $(\mathbb{F}_2^n,+)$ (so $X(0)=Z(0)=I$ and $X(a)X(a') = X(a+a')$) and $Z(b)X(a) = (-1)^{a\cdot b}X(a)Z(b)$. Then there are a finite set $L$ and a unitary $\Phi:\mathbb{C}^{2^n}\otimes\mathbb{C}^L\to\mathbb{C}^\kappa$ with

$$
X(a) = \Phi\,(X^a\otimes I)\,\Phi^*,\qquad Z(b) = \Phi\,(Z^b\otimes I)\,\Phi^*\qquad\text{for all }a,b .
$$

Equivalently, every representation of the Pauli group modulo $i$ in which the central element acts as $-1$ is a multiple of the standard one.

## Proof sketch

The $Z(b)$ commute and $\Pi = 2^{-n}\sum_bZ(b)$ projects onto their joint $+1$ eigenspace. Character orthogonality gives $\Pi X(c)\Pi = [c=0]\Pi$ and $\sum_zX(z)\Pi X(z) = I$. Choosing an isometry $E$ onto the range of $\Pi$ and setting $\Phi(|z\rangle\otimes\ell) = X(z)E\ell$ gives a unitary; $X(a)$ shifts $z$ by $a$ and $Z(b)$ acts on $X(z)E\ell$ by the sign $(-1)^{b\cdot z}$, which is the intertwining.

## Depends on

- [Pauli strings and the Pauli group modulo $i$ as a Heisenberg group](pauli-group-modulo-i.md)

## Sources

- A. Natarajan and T. Vidick, "A quantum linearity test for robustly verifying entanglement", Proceedings of the 49th Annual ACM Symposium on Theory of Computing (STOC 2017), 1003-1015, 2017.
