# Symplectic Gram–Schmidt over $\mathbb{F}_2$

Let $\omega$ be the [symplectic product](symplectic-product-of-pauli-operators.md) on $\mathbb{F}_2^{2n}$ and let
$V \subseteq \mathbb{F}_2^{2n}$ be an isotropic subspace ($\omega(v, w) = 0$ for all $v, w \in V$) of dimension $n - k$.
Its symplectic complement $V^{\perp} = \{ u : \omega(u, v) = 0 \ \forall v \in V \}$ has dimension $n + k$ and contains
$V$, and there are vectors $z_1, \dots, z_k, x_1, \dots, x_k \in V^{\perp}$ with

$$\omega(z_i, z_j) = \omega(x_i, x_j) = 0, \qquad \omega(z_i, x_j) = \delta_{ij},$$

such that $V^{\perp} = V \oplus \operatorname{span}(z_1, \dots, z_k, x_1, \dots, x_k)$. Proof: extend $V$ to a maximal
isotropic subspace $V \oplus \operatorname{span}(z_1, \dots, z_k)$ inside $V^{\perp}$; nondegeneracy of $\omega$ gives
$x_j \in V^{\perp}$ pairing with $z_j$ only, and replacing $x_2, \dots, x_k$ in turn by $x_j + \sum_{i < j} \omega(x_i, x_j) z_i$,
with the $x_i$ already replaced, makes them isotropic while keeping $\omega(z_i, x_j) = \delta_{ij}$, as in Gram–Schmidt
orthogonalization.

## Depends on

- [Symplectic product of Pauli operators](symplectic-product-of-pauli-operators.md)

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.9.4 ("By invoking a Gram-Schmidt orthonormalization procedure, we can choose these generators, denoted $\bar X_i$, to diagonalize the symplectic form", equation (7.145)).
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 4.1, equations (4.3)–(4.6) (the standard form and the encoded $\bar X$ and $\bar Z$ operators).
