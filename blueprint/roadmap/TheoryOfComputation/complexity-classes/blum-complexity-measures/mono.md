# Blum classes are monotone in the bound

Let $\Phi$ be a Blum complexity measure, let $t, t' : \mathbb{N} \to \mathbb{N}$ satisfy
$t(n) \le t'(n)$ for all sufficiently large $n$, and let $f$ be a partial function from
$\mathbb{N}$ to $\mathbb{N}$. If $f$ belongs to the Blum class of $t$, that is, some program $e$
computes $f$ and, for all sufficiently large $n$, $\Phi_e(n)$ is defined and at most $t(n)$, then
$f$ belongs to the Blum class of $t'$.

## Sources

- M. Blum, "A machine-independent theory of the complexity of recursive functions", *Journal of the ACM* 14 (1967), 322–336, Definition 2.
