# Kumar: every homogeneous polynomial lies in the border of top-fan-in d+1 depth-three circuits

Over $\mathbb{C}$, every homogeneous polynomial $P$ of degree $d$ in $n$ variables is a limit of polynomials computed by $\Sigma\Pi\Sigma$ circuits of top fan-in at most $d + 1$: there are $\Sigma\Pi\Sigma$ circuits $C_\varepsilon$ of top fan-in $d+1$, whose coefficients are rational functions of $\varepsilon$, with $C_\varepsilon \to P$ as $\varepsilon \to 0$. Moreover, if $P$ has an arithmetic circuit of size $s$, then for every $t \le d$, $P$ lies in the border of $\Sigma\Pi\Sigma$ circuits of top fan-in $s^{O(t)}$ and formal degree $s^{O(d/t)}$. By contrast, some homogeneous quadratics require top fan-in $\Omega(n)$ in exact depth-three circuits.

## Proof sketch

If $P = \sum_{i=1}^{r} \ell_i^d$ is a sum of powers of linear forms, then $\prod_{i=1}^{r}(1 + \varepsilon \ell_i^d) = 1 + \varepsilon P + O(\varepsilon^2)$, and each factor $1 + \varepsilon\ell_i^d$ factors into $d$ affine linear forms over $\mathbb{C}$ using roots of $-1/\varepsilon$; so $P = \lim \bigl(\prod - 1\bigr)/\varepsilon$ is a border sum of two products, after grouping, with top fan-in $2$ but large formal degree. Applying this to the Waring decomposition of the homogeneous components gives the first statement. For the tradeoff (Kumar's first proof of Theorem 1.5), drop the variables that do not occur, so that $s \ge n$, and run the depth-four reduction with bottom degree $a = \lceil d/t \rceil$ in place of $\sqrt{d}$ (the same top-down cutting; Tavenas's Lemma 3 gives homogeneous $\Sigma\Pi^{[15b]}\Sigma\Pi^{[d/b]}$ circuits for every $b < d$): $P$ becomes a homogeneous $\Sigma^{[T]}\Pi^{[O(d/a)]}\Sigma\Pi^{[a]}$ circuit with $T = s^{O(d/a)}$ and each bottom polynomial a sum of $n^{O(a)}$ monomials. The first statement approximates each bottom $\Sigma\Pi^{[a]}$ subcircuit by a $\Sigma\Pi\Sigma$ circuit of top fan-in $a + 1$ and formal degree $n^{O(a)}$, and expanding the products at the second level gives a border $\Sigma\Pi\Sigma$ circuit of top fan-in $T\,(a+1)^{O(d/a)}$ and formal degree $O(d/a)\,n^{O(a)}$, which are the stated $s^{O(t)}$ and $s^{O(d/t)}$. The depth-four reduction and Fischer's identity hold over every field of characteristic $0$, $\mathbb{C}$ included.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Proof depends on

- [Agrawal–Vinay–Koiran–Tavenas reduction to depth four](agrawal-vinay-tavenas.md)
- [Fischer's identity: products of variables as sums of powers of linear forms](fischer-identity.md)

## Sources

- M. Kumar, "On the power of border of depth-3 arithmetic circuits", ACM Transactions on Computation Theory 12 (2020), arXiv:1804.03303 (Theorems 1.2 and 1.5; first proof of Theorem 1.5).
- S. Tavenas, "Improved bounds for reduction to depth 4 and depth 3", MFCS (2013); Information and Computation 240 (2015) 2-11; arXiv:1304.5777 (Lemma 3 and the proof of Theorem 1).
