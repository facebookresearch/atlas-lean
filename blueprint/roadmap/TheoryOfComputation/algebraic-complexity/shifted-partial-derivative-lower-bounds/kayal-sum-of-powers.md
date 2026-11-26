# Kayal: sums of powers of low-degree polynomials cannot compute the product of variables

Let $\mathbb{F}$ have characteristic $0$. If $x_1 x_2 \cdots x_n = \sum_{i=1}^{s} Q_i^{e_i}$ with $\deg Q_i \le t$, then

$$
s \ge \exp\Bigl(\Omega\Bigl(\frac{n}{t}\Bigr)\Bigr).
$$

In particular, for $t = O(1)$ the product of variables needs exponentially many powers of bounded-degree polynomials.

## Proof sketch

For a power $Q^{e}$ every $k$-th derivative is of the form $Q^{e-k} R$ with $\deg R \le (t-1)k$, so its shifted partials span is small; on the other hand the $k$-th derivatives of $x_1 \cdots x_n$ are the $\binom{n}{k}$ distinct multilinear monomials of degree $n-k$, whose shifts by degree-$\ell$ monomials span a space close to the full space for suitable $k \approx n/t$. Comparing the two dimensions gives the bound.

## Depends on

- [The dimension of shifted partial derivatives](shifted-partials-measure.md)

## Proof depends on

- [The dimension of shifted partial derivatives](shifted-partials-measure.md)

## Sources

- N. Kayal, "An exponential lower bound for the sum of powers of bounded degree polynomials", ECCC TR12-081 (2012).
