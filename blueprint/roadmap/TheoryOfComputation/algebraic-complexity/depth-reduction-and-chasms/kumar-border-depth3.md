# Kumar: every homogeneous polynomial lies in the border of top-fan-in d+1 depth-three circuits

Over $\mathbb{C}$, every homogeneous polynomial $P$ of degree $d$ in $n$ variables is a limit of polynomials computed by $\Sigma\Pi\Sigma$ circuits of top fan-in at most $d + 1$: there are $\Sigma\Pi\Sigma$ circuits $C_\varepsilon$ of top fan-in $d+1$, whose coefficients are rational functions of $\varepsilon$, with $C_\varepsilon \to P$ as $\varepsilon \to 0$. Moreover, if $P$ has an arithmetic circuit of size $s$, then for every $t \le d$, $P$ lies in the border of $\Sigma\Pi\Sigma$ circuits of top fan-in $s^{O(t)}$ and formal degree $s^{O(d/t)}$. By contrast, some homogeneous quadratics require top fan-in $\Omega(n)$ in exact depth-three circuits.

## Proof sketch

If $P = \sum_{i=1}^{r} \ell_i^d$ is a sum of powers of linear forms, then $\prod_{i=1}^{r}(1 + \varepsilon \ell_i^d) = 1 + \varepsilon P + O(\varepsilon^2)$, and each factor $1 + \varepsilon\ell_i^d$ factors into $d$ affine linear forms over $\mathbb{C}$ using roots of $-1/\varepsilon$; so $P = \lim \bigl(\prod - 1\bigr)/\varepsilon$ is a border sum of two products, after grouping, with top fan-in $2$ but large formal degree. Applying this to the Waring decomposition of the homogeneous components and combining with depth reduction gives the stated tradeoffs.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Proof depends on

- [Gupta–Kamath–Kayal–Saptharishi: the chasm at depth three](gkks-depth-three-chasm.md)
- [Fischer's identity: products of variables as sums of powers of linear forms](fischer-identity.md)

## Sources

- M. Kumar, "On the power of border of depth-3 arithmetic circuits", ACM Transactions on Computation Theory 12 (2020), arXiv:1804.03303.
