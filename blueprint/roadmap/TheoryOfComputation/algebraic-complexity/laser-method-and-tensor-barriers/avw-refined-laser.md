# Alman–Vassilevska Williams: refined laser method and omega < 2.37286

Let $T$ be a tensor over $X, Y, Z$ with partitions $X = X_1 \cup \dots \cup X_n$, $Y = Y_1 \cup \dots \cup Y_n$, $Z = Z_1 \cup \dots \cup Z_n$, write $T_{ijk}$ for the restriction of $T$ to $X_i, Y_j, Z_k$, and let $S = \{(i,j,k) \in [n]^3 : T_{ijk} \ne 0\}$. Suppose that $(i,i,i) \in S$ for every $i \in [n]$, that for every other $(i,j,k) \in S$ the three indices $i, j, k$ are pairwise distinct, and that $m := (|S| - n)/n \ge 1$. Then there is a set $I \subseteq [n]$ with

$$
|I| \ge \frac{2n}{3\sqrt{3m}}
$$

such that zeroing out every $X_j, Y_j, Z_j$ with $j \notin I$ turns $T$ into the direct sum $\bigoplus_{i \in I} T_{iii}$. In the laser method this replaces the greedy final step: if a direct sum of $B$ subtensors consistent with the target distribution $\alpha$ remains together with about $m \cdot B$ further subtensors consistent with other distributions having the same marginals as $\alpha$, the greedy argument keeps $B/\Theta(m)$ independent $\alpha$-consistent subtensors, and the theorem keeps $B/\Theta(\sqrt{m})$. This raises the value bound by a factor $\Theta(\sqrt{m})$ whenever $m \gg 1$, and applied to $\mathrm{CW}_5^{\otimes 32}$ it gives the bound $\omega < 2.37286$ (more precisely $\omega < 2.3728596$).

## Proof sketch

Put each index in a random set $R$ independently with probability $p = 1/\sqrt{3m}$. Let $A$ be the set of first indices $i$ of the triples $(i,j,k) \in S$ with pairwise distinct indices that lie entirely in $R$, and let $I = R \setminus A$. Then $\mathbb{E}|I| \ge pn - p^3 nm = 2n/(3\sqrt{3m})$, so some outcome achieves this. Zeroing out the blocks outside $I$ keeps every $T_{iii}$ with $i \in I$, and kills every other triple of $S$: either one of its indices lies outside $R$, or all lie in $R$ and its first index lies in $A$.

## Depends on

- [The Coppersmith–Winograd tensor](cw-tensor.md)
- [The value of a tensor in the laser method](tensor-value.md)

## Proof depends on

- [The laser method bound on omega from tensor values](laser-method-bound.md)
- [Alman–Vassilevska Williams 2020 bound on the square exponent](../matrix-multiplication-exponent/alman-vassilevska-williams2020-upper.md)

## Sources

- J. Alman, V. Vassilevska Williams, "A refined laser method and faster matrix multiplication", SODA (2021), arXiv:2010.05846 (Section 1.1, Theorem 3.1).
