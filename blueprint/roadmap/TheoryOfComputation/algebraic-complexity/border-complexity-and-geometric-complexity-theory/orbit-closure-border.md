# Orbit closures and border complexity of polynomials

Let $V_n = \mathbb{C}[x_1, \dots, x_n]_d$ be the space of homogeneous polynomials of degree $d$ with the action $(g \cdot f)(x) = f(g^{-1}x)$ of $\mathrm{GL}_n(\mathbb{C})$. The **orbit closure** $\overline{\mathrm{GL}_n \cdot f}$ is the Zariski closure (equivalently the Euclidean closure) of the orbit of $f$. For a complexity measure $c$ on polynomials (circuit size, formula size, Waring rank, determinantal complexity), the **border complexity** $\underline{c}(f)$ is the least $s$ such that $f$ is a limit of polynomials $f_\varepsilon$ with $c(f_\varepsilon) \le s$. For example, the **border Waring rank** $\underline{\mathrm{WR}}(f)$ is the least $r$ with $f \in \overline{\{\ell_1^d + \cdots + \ell_r^d\}}$.

## Depends on

- [Valiant's VP versus VNP conjecture](../valiant-s-vp-versus-vnp-conjecture.md)

## Sources

- K. D. Mulmuley, M. Sohoni, "Geometric complexity theory I: an approach to the P vs. NP and related problems", SIAM Journal on Computing 31 (2001) 496-526.
- P. Bürgisser, C. Ikenmeyer, G. Panova, "No occurrence obstructions in geometric complexity theory", Journal of the American Mathematical Society 32 (2019) 163-193; FOCS (2016), arXiv:1604.06431.
- P. Dutta, F. Gesmundo, C. Ikenmeyer, G. Jindal, V. Lysikov, "Geometric complexity theory for product-plus-power", arXiv:2211.07055 (2022), ECCC TR22-157.
