# The Cook–Mertz register procedure for Tree Evaluation

Let $\mathbb{F}$ be a finite field containing a primitive $m$-th root of unity $\omega$ with $m$ larger than the degree $d\ell$ of the multilinear extensions $\tilde f_u:\mathbb{F}^{d\ell}\to\mathbb{F}^{\ell}$ of the gate functions, and embed $\{0,1\}^{\ell}\subseteq\mathbb{F}^{\ell}$. There is a recursive procedure $P_u(c)$, defined for every node $u$ and coefficient $c\in\mathbb{F}$, acting on a file of $d+1$ registers each holding a vector in $\mathbb{F}^{\ell}$, such that **for all initial register contents** $P_u(c)$ adds $c\cdot\mathrm{val}(u)$ to its output register and leaves every other register unchanged, and $P_u(-c)$ undoes $P_u(c)$. For an internal node, $P_u(c)$ makes $m$ rounds; round $j$ multiplies each child register by $\omega^{j}$ and calls $P_{u_i}(1)$, so the registers hold $\mathrm{val}(u_i)+\omega^j\tau_i$ with $\tau_i$ the initial content of the $i$-th child register; it adds $\frac{c}{m}\tilde f_u(\text{child registers})$ to the output register, then calls $P_{u_i}(-1)$ and multiplies back by $\omega^{-j}$. Since $\frac1m\sum_{j}p(y+\omega^j\tau)=p(y)$ for every polynomial $p$ of degree $<m$, the rounds together add exactly $c\,\tilde f_u(\mathrm{val}(u_1),\dots,\mathrm{val}(u_d))$.

## Proof sketch

During round $j$ the child registers hold $y+\omega^j\tau$, where $y=(\mathrm{val}(u_i))_i$ and $\tau$ is their initial content. The map $z\mapsto\tilde f_u(y+z\tau)$ is a polynomial of degree $<m$, and $\sum_{j=1}^{m}\omega^{jk}=0$ for $0<k<m$, so the average of its values at the $m$ roots of unity is its constant term $\tilde f_u(y)$. The inverse calls and the multiplications by $\omega^{-j}$ restore all registers other than the output exactly, by induction on height.

## Depends on

- [The Tree Evaluation problem](tree-evaluation-problem.md)

## Sources

- James Cook and Ian Mertz, "Tree Evaluation is in Space O(log n · log log n)", Proceedings of the 56th Annual ACM Symposium on Theory of Computing (STOC 2024), pp. 1268–1278 (ECCC TR23-174).
