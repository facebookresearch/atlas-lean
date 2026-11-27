# Tardos: an exponential gap between monotone and non-monotone circuit complexity

There is a monotone graph property $T_n$ on $n$-vertex graphs that is computable in polynomial time, hence by Boolean circuits of polynomial size, but every monotone circuit computing $T_n$ has size

$$
\exp\Bigl(\Omega\bigl((n/\log n)^{1/3}\bigr)\Bigr).
$$

The property is a threshold of Tardos's function

$$
\varphi(X) = \bigl\lfloor g(\overline{X}, n^{-2}) + e(X)\, n^{-2} \bigr\rceil,
$$

where $\lfloor\cdot\rceil$ is the nearest integer, $e(X)$ the number of edges of $X$, and $g(Y, \varepsilon)$ the Grötschel–Lovász–Schrijver approximation of the Lovász theta function, computed in polynomial time by the ellipsoid method with $\vartheta(Y) \le g(Y, \varepsilon) \le \vartheta(Y) + \varepsilon$. The function $\varphi$ is polynomial-time computable, monotone, and satisfies $\omega(X) \le \varphi(X) \le \chi(X)$; take $T_n(X) = 1$ iff $\varphi(X) > f(n)$ with $f(n) = (n/\log n)^{2/3}/4$.

## Proof sketch

Since $\omega(X) \le \vartheta(\overline{X}) \le \chi(X)$, $0 \le g(\overline{X}, n^{-2}) - \vartheta(\overline{X}) \le n^{-2}$ and $e(X)\, n^{-2} \le (n-1)/(2n)$, for $n \ge 3$ the sum is at least $\omega(X)$ and less than $\chi(X) + 1/2$, and rounding to the nearest integer gives $\omega(X) \le \varphi(X) \le \chi(X)$. Adding an edge to $X$ raises $e(X)\, n^{-2}$ by $n^{-2}$ and lowers $g(\overline{X}, n^{-2})$ by at most $n^{-2}$, as $\vartheta(\overline{X})$ does not decrease; so $\varphi$ is monotone, while the exact rounding of $g(\overline{X}, \varepsilon)$ alone need not be. Razborov's argument, in the Alon–Boppana form, applies to any monotone graph function between the clique number and the chromatic number: for $3 \le f(n) \le (n/\log n)^{2/3}/4$, deciding whether $\varphi(X) \le f(n)$, that is computing $T_n$, needs monotone circuits of size $\exp(c \cdot f(n)^{1/2})$, which for the largest $f(n)$ is $\exp(\Omega((n/\log n)^{1/3}))$.

## Depends on

- [Lovász theta function](../../../GraphTheory/graph-invariants-and-labelings/theta-function-of-a-graph/lovasz-theta.md)

## Proof depends on

- [Alon–Boppana: monotone circuits for clique need exponential size](../monotone-circuit-lower-bound-for-clique/alon-boppana-monotone-clique.md)
- [Razborov: monotone circuits for clique need superpolynomial size](../monotone-circuit-lower-bound-for-clique/razborov-monotone-clique.md)

## Sources

- É. Tardos, "The gap between monotone and non-monotone circuit complexity is exponential", Combinatorica 8(1) (1988) 141-142.
- N. Alon, R. B. Boppana, "The monotone circuit complexity of Boolean functions", Combinatorica 7 (1987) 1-22.
