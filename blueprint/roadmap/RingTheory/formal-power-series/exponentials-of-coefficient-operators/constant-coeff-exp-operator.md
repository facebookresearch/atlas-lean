# The operator exponential preserves the constant coefficient

Let $A$ be a commutative $\mathbb{Q}$-algebra and $A[[X]]$ the ring of formal power series in
variables $(X_i)_{i \in \sigma}$, with $[X^d] f$ the coefficient of $X^d$ for a finitely supported
exponent $d \colon \sigma \to \mathbb{N}$, $|d|$ its total degree, $e_i$ the exponent of $X_i$ and
$\partial_i$ the partial derivative in $X_i$. For a family $(O_i)_{i \in \sigma}$ of
$\mathbb{Q}$-linear maps $A \to A$, write $\widehat{O}_i$ for $O_i$ applied to every coefficient of
a power series, and $\mathcal{O} = \sum_i X_i \widehat{O}_i$ for the coefficient operator:
$[X^d] \mathcal{O}(f) = \sum_{i \,:\, d_i > 0} O_i([X^{d - e_i}] f)$. The exponential of
$\mathcal{O}$ is defined by
$[X^d] e^{\mathcal{O}}(f) = [X^d] \sum_{n \le |d|} \mathcal{O}^n(f) / n!$. For every $f \in A[[X]]$,
the constant coefficient of $e^{\mathcal{O}}(f)$ equals the constant coefficient of $f$.
