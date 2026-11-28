# Fischer's identity: products of variables as sums of powers of linear forms

Let $\mathbb{F}$ be a field of characteristic $0$ or of characteristic greater than $d$. Then

$$
x_1 x_2 \cdots x_d = \frac{1}{2^{d-1} d!} \sum_{\varepsilon \in \{\pm 1\}^{d-1}} \Bigl(\prod_{i=2}^{d} \varepsilon_i\Bigr) \bigl(x_1 + \varepsilon_2 x_2 + \cdots + \varepsilon_d x_d\bigr)^{d}.
$$

Consequently, a product of $d$ linear forms is a linear combination of $2^{d-1}$ $d$-th powers of linear forms.

## Proof sketch

Expand each power by the multinomial theorem. A monomial $\prod_i x_i^{e_i}$ with $\sum e_i = d$ receives coefficient proportional to $\sum_\varepsilon \prod_{i \ge 2} \varepsilon_i^{1 + e_i}$, which vanishes unless every $e_i$ with $i \ge 2$ is odd; with total degree $d$ and $d$ variables this forces $e_i = 1$ for all $i$. The surviving coefficient is $2^{d-1} d!$.

## Proof depends on

- [Homogeneous depth-four circuits with bounded bottom fan-in](homogeneous-depth-four.md)

## Sources

- I. Fischer, "Sums of like powers of multivariate linear forms", Mathematics Magazine 67 (1994) 59-61.
- A. Gupta, P. Kamath, N. Kayal, R. Saptharishi, "Arithmetic circuits: a chasm at depth three", FOCS (2013); SIAM Journal on Computing 45 (2016) 1064-1079.
