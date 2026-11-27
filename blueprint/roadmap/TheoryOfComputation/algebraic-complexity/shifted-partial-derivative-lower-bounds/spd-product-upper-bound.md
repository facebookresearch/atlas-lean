# Shifted partials of a product of low-degree polynomials

Let $T = Q_1 Q_2 \cdots Q_a$ with each $Q_j \in \mathbb{F}[x_1, \dots, x_n]$ of degree at most $t$. Then for all $k \le a$ and $\ell \ge 0$,

$$
\mathrm{SP}_{k,\ell}(T) \le \binom{a + k}{k} \binom{n + \ell + (t - 1)k}{n}.
$$

Consequently a homogeneous $\Sigma\Pi^{[a]}\Sigma\Pi^{[t]}$ circuit with $s$ product gates computes a polynomial with $\mathrm{SP}_{k,\ell} \le s \binom{a+k}{k}\binom{n + \ell + (t-1)k}{n}$.

## Proof sketch

By the product rule every $k$-th order derivative of $T$ is a sum of terms of the form $\bigl(\prod_{j \notin S} Q_j\bigr) \cdot R$, where $S$ is a multiset of at most $k$ indices and $R$ has degree at most $(t-1)k$. Hence every shifted partial lies in the span of $\prod_{j \notin S} Q_j \cdot m'$ with $m'$ of degree at most $\ell + (t-1)k$; counting choices of $S$ and of $m'$ gives the bound, and subadditivity handles the outer sum.

## Depends on

- [The dimension of shifted partial derivatives](shifted-partials-measure.md)
- [Homogeneous depth-four circuits with bounded bottom fan-in](../depth-reduction-and-chasms/homogeneous-depth-four.md)

## Sources

- A. Gupta, P. Kamath, N. Kayal, R. Saptharishi, "Approaching the chasm at depth four", Journal of the ACM 61 (2014); CCC (2013).
- N. Kayal, "An exponential lower bound for the sum of powers of bounded degree polynomials", ECCC TR12-081 (2012).
