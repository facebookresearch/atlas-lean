# Formal exponential of a coefficient operator

Let $A$ be a commutative $\mathbb{Q}$-algebra and $A[[X]]$ the ring of formal power series in
variables $(X_i)_{i \in \sigma}$, with $[X^d] f$ the coefficient of $X^d$ for a finitely supported
exponent $d \colon \sigma \to \mathbb{N}$, $|d|$ its total degree, $e_i$ the exponent of $X_i$ and
$\partial_i$ the partial derivative in $X_i$. For a family $(O_i)_{i \in \sigma}$ of
$\mathbb{Q}$-linear maps $A \to A$, write $\widehat{O}_i$ for $O_i$ applied to every coefficient of
a power series, and $\mathcal{O} = \sum_i X_i \widehat{O}_i$ for the coefficient operator:
$[X^d] \mathcal{O}(f) = \sum_{i \,:\, d_i > 0} O_i([X^{d - e_i}] f)$. The exponential of
$\mathcal{O}$ is the $\mathbb{Q}$-linear map $e^{\mathcal{O}}$ of $A[[X]]$ defined coefficientwise
by

$$[X^d] e^{\mathcal{O}}(f) = [X^d] \sum_{n \le |d|} \frac{\mathcal{O}^n(f)}{n!}.$$

Only the iterates $\mathcal{O}^n$ with $n \le |d|$ contribute to the coefficient of $X^d$, since
$\mathcal{O}^n(f)$ has no monomials of total degree less than $n$.
