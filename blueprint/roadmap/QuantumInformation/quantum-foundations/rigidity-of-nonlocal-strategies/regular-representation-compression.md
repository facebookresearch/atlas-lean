# Compression of the regular representation (first step of Gowers-Hatami stability)

Let $G$ be a finite group, $f:G\to U(\mathbb{C}^\iota)$ any map into unitaries, $g$ the right regular representation on $\mathbb{C}^\iota\otimes\mathbb{C}^G$, $(g(y)w)(i,z) = w(i,zy)$, and $V\psi = |G|^{-1/2}\sum_xf(x)\psi\otimes|x\rangle$. Then $V$ is an isometry, $V^*g(y)V = \mathbb{E}_zf(z)^*f(zy)$, and for every state $\varphi$ on $M_\iota(\mathbb{C})$

$$
\mathbb{E}_y\|f(y)-V^*g(y)V\|_\varphi^2\le\mathbb{E}_{x,y}\|f(x)f(y)-f(xy)\|_\varphi^2 .
$$

If $f$ is an exact representation then $V^*g(y)V = f(y)$ for all $y$.

## Proof sketch

The rows of $Vf(y)-g(y)V$ are the multiplicative defects $|G|^{-1/2}(f(z)f(y)-f(zy))$, so its Gram matrix averaged over $y$ is the averaged Gram matrix of the defects. Writing $f(y)-V^*g(y)V = V^*(Vf(y)-g(y)V)$ and using that $V^*$ is a contraction gives the bound in every state.

## Depends on

- [States on star-ordered algebras, state-dependent norm and approximation](../states-and-measurements-on-operator-algebras/algebraic-states-and-state-dependent-norm.md)

## Sources

- W. T. Gowers and O. Hatami, "Inverse and stability theorems for approximate representations of finite groups", Sbornik: Mathematics 208:1784-1817, 2017.
- M. de la Salle, "Spectral gap and stability for groups and non-local games", Journal de l'Ecole polytechnique - Mathematiques 12:1417-1444, 2025.
