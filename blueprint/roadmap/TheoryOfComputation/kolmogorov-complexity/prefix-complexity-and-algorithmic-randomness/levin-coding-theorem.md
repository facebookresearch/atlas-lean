# Algorithmic probability and Levin's coding theorem

For a prefix-free method $M$ let $\mathbf{m}_M(x) = \sum_{p : M(p) = x} 2^{-|p|}$ be the *algorithmic probability* of $x$; then $\sum_x \mathbf{m}_M(x) = \Omega_M \le 1$. For the universal prefix-free method, $\mathbf{m} = \mathbf{m}_U$ is a maximal lower semicomputable semimeasure: for every lower semicomputable $\mu$ with $\sum_x \mu(x) \le 1$ there is $c > 0$ with $\mu(x) \le c\, \mathbf{m}(x)$. *Coding theorem:*

$$K(x) = -\log_2 \mathbf{m}(x) + O(1).$$

## Proof sketch

$2^{-K(x)} \le \mathbf{m}(x)$ since a shortest program contributes. Conversely, enumerate lower approximations of $\mathbf{m}$ and request, via Kraft–Chaitin, a codeword of length $k + 1$ for $x$ whenever $\mathbf{m}(x)$ is seen to exceed $2^{-k}$; the total requested weight is at most $\sum_x 2 \mathbf{m}(x) \cdot \frac12 \le 1$, giving $K(x) \le -\log_2\mathbf{m}(x) + O(1)$.

## Depends on

- [Prefix-free Kolmogorov complexity](prefix-free-kolmogorov-complexity.md)
- [Chaitin's halting probability Ω](chaitins-halting-probability.md)

## Proof depends on

- [The online Kraft–Chaitin theorem](online-kraft-chaitin-theorem.md)

## Sources

- L. A. Levin, "Randomness Conservation Inequalities; Information and Independence in Mathematical Theories", Information and Control 61(1), 1984.
- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
- A. Shen, V. A. Uspensky and N. Vereshchagin, "Kolmogorov Complexity and Algorithmic Randomness", American Mathematical Society, 2017.
