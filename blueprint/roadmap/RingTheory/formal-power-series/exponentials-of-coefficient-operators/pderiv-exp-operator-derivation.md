# Gradient law for the exponential of commuting coefficient derivations

Let $A$ be a commutative $\mathbb{Q}$-algebra and $A[[X]]$ the ring of formal power series in
variables $(X_i)_{i \in \sigma}$, with $[X^d] f$ the coefficient of $X^d$ for a finitely supported
exponent $d \colon \sigma \to \mathbb{N}$, $|d|$ its total degree, $e_i$ the exponent of $X_i$ and
$\partial_i$ the partial derivative in $X_i$. For a family $(O_i)_{i \in \sigma}$ of
$\mathbb{Q}$-linear maps $A \to A$, write $\widehat{O}_i$ for $O_i$ applied to every coefficient of
a power series, and $\mathcal{O} = \sum_i X_i \widehat{O}_i$ for the coefficient operator:
$[X^d] \mathcal{O}(f) = \sum_{i \,:\, d_i > 0} O_i([X^{d - e_i}] f)$. When the $O_i = D_i$ are
$\mathbb{Q}$-linear derivations of $A$, write $\mathcal{D}$ for the coefficient operator and
$e^{\mathcal{D}}$ for its exponential, defined by
$[X^d] e^{\mathcal{D}}(f) = [X^d] \sum_{n \le |d|} \mathcal{D}^n(f) / n!$. Suppose that the
derivations commute pairwise: $D_i D_j = D_j D_i$ for all $i, j$. Then for every $i$ and every
$f \in A[[X]]$,

$$\partial_i\, e^{\mathcal{D}}(f) = e^{\mathcal{D}}(\partial_i f) + e^{\mathcal{D}}\bigl(\widehat{D}_i(f)\bigr).$$
