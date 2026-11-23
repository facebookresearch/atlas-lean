# Random-current representation

Let $G = (V, E)$ be a finite simple graph, $\beta \in \mathbb{R}$, $J$ real couplings and $A \subseteq V$; a current $n$ assigns a multiplicity $n_e \in \mathbb{N}$ to every edge, its [sources](sources.md) $\partial n$ are the vertices of odd total incident multiplicity, and its [weight](weight.md) is $w(n) = \prod_{e \in E} (\beta J_e)^{n_e}/n_e!$. Then

$$\langle \sigma_A \rangle_{\beta, J} = \frac{Z(\partial = A)}{Z(\partial = \emptyset)},$$

with $\langle \sigma_A \rangle_{\beta, J}$ the zero-field [correlation with couplings](expectation-j.md) $J$, $\sigma_A = \prod_{x \in A} \sigma_x$ and $Z(\partial = A) = \sum_{\partial n = A} w(n)$ the [current sum](current-sum.md) (M. Aizenman, *Geometric analysis of $\varphi^4$ fields and Ising models*, Comm. Math. Phys. 86 (1982) 1–48; J. Ginibre (1970); H. Duminil-Copin, *Random currents expansion of the Ising model*, arXiv:1607.06933 (2016)).
