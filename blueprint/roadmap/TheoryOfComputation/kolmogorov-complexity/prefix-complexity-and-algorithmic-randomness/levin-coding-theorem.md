# Algorithmic probability and Levin's coding theorem

For a prefix-free method $M$ let $\mathbf{m}_M(x) = \sum_{p : M(p) = x} 2^{-|p|}$ be the *algorithmic probability* of $x$; then $\sum_x \mathbf{m}_M(x) = \Omega_M \le 1$. A function $\mu$ on strings with values in $[0,\infty)$ is a *lower semicomputable semimeasure* if it is enumerable from below and $\sum_x \mu(x) \le 1$. There is a maximal lower semicomputable semimeasure $\mathbf{m}$, the *a priori probability*: for every lower semicomputable semimeasure $\mu$ there is $c > 0$ with $\mu(x) \le c\, \mathbf{m}(x)$ for all $x$. *Coding theorem:*

$$K(x) = -\log_2 \mathbf{m}(x) + O(1).$$

## Proof sketch

Existence: run a randomly chosen probabilistic machine without input; its output distribution dominates each enumerable-from-below semimeasure up to the probability of choosing that machine. Since $x \mapsto 2^{-K(x)}$ is a lower semicomputable semimeasure, $2^{-K(x)} \le c\,\mathbf{m}(x)$. Conversely, enumerate lower approximations of $\mathbf{m}$ and request, via Kraft–Chaitin, a codeword of length $k + 1$ for $x$ whenever $\mathbf{m}(x)$ is seen to exceed $2^{-k}$; for each $x$ the requests have lengths $k+1$ for the $k$ with $2^{-k} < \mathbf{m}(x)$, of total weight $\sum_{k : 2^{-k} < \mathbf{m}(x)} 2^{-k-1} < \mathbf{m}(x)$, so the total requested weight is less than $\sum_x \mathbf{m}(x) \le 1$, giving $K(x) \le -\log_2\mathbf{m}(x) + O(1)$.

Derived (not displayed as one statement in the cited sources): for the universal prefix-free method $U$, $\mathbf{m}_U$ is itself a maximal lower semicomputable semimeasure. Indeed $\mathbf{m}_U$ is lower semicomputable with $\sum_x \mathbf{m}_U(x) \le 1$, so $\mathbf{m}_U \le c\,\mathbf{m}$, while a shortest program gives $\mathbf{m}_U(x) \ge 2^{-K(x)} \ge 2^{-O(1)}\mathbf{m}(x)$ by the coding theorem.

## Depends on

- [Prefix-free Kolmogorov complexity](prefix-free-kolmogorov-complexity.md)
- [Chaitin's halting probability Ω](chaitins-halting-probability.md)

## Proof depends on

- [The online Kraft–Chaitin theorem](online-kraft-chaitin-theorem.md)

## Sources

- A. Shen, "Algorithmic Information Theory and Kolmogorov Complexity", lecture notes, Uppsala University, 2007 (author's copy), Section 33, Theorem 24 (maximal enumerable-from-below semimeasure, a priori probability), and Section 36, Theorem 28 ($\mathrm{KP}(x) = -\log m(x) + O(1)$).
- L. A. Levin, "Randomness Conservation Inequalities; Information and Independence in Mathematical Theories", Information and Control 61(1), 15–37, 1984.
- G. J. Chaitin, "A Theory of Program Size Formally Identical to Information Theory", Journal of the ACM 22(3), 329–340, 1975, Theorem 3.5.
- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
- A. Shen, V. A. Uspensky and N. Vereshchagin, "Kolmogorov Complexity and Algorithmic Randomness", American Mathematical Society, 2017.
