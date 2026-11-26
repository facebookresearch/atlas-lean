# The Cook–Mertz register procedure for Tree Evaluation

Let $\mathbb{F}$ be a finite field containing a primitive $m$-th root of unity $\omega$ with $m$ larger than the degree $d\ell$ of the multilinear extensions $\tilde f_u:\mathbb{F}^{d\ell}\to\mathbb{F}^{\ell}$ of the gate functions, and embed $\{0,1\}^{\ell}\subseteq\mathbb{F}^{\ell}$. There is a recursive procedure $P_u(c)$, defined for every node $u$ and coefficient $c\in\mathbb{F}$, acting on a file of $d+1$ registers each holding a vector in $\mathbb{F}^{\ell}$, such that **for all initial register contents** $P_u(c)$ adds $c\cdot\mathrm{val}(u)$ to its output register and leaves every other register unchanged, and $P_u(-c)$ undoes $P_u(c)$. For an internal node, $P_u(c)$ makes $m$ rounds; round $j$ calls $P_{u_i}(\omega^{j})$ for each child to shift the child registers, adds $c\,\omega^{-j}\cdot\frac{1}{m}\tilde f_u(\text{child registers})$ to the output register, and calls $P_{u_i}(-\omega^{j})$ to restore them; the averaging over the $m$ roots of unity cancels every term of the polynomial except the one that evaluates $\tilde f_u$ at the true child values.

## Proof sketch

Write the child registers as $x_i+\omega^j\,\mathrm{val}(u_i)$ during round $j$. As a polynomial in $\omega^j$ of degree $< m$, $\tilde f_u(x+\omega^j y)\,\omega^{-j}$ averages over $j$ to the coefficient that, after one more symmetrization, is $\tilde f_u(y)$; with the inverse calls, all register contents other than the output are restored exactly, by induction on height.

## Depends on

- [The Tree Evaluation problem](tree-evaluation-problem.md)

## Sources

- James Cook and Ian Mertz, "Tree Evaluation is in Space O(log n · log log n)", Electronic Colloquium on Computational Complexity, report TR23-174, 2023.
- Oded Goldreich, "On the Cook–Mertz Tree Evaluation procedure", Electronic Colloquium on Computational Complexity, report TR24-109, 2024.
