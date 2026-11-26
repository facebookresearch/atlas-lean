# The Coppersmith–Winograd tensor has border rank q+2

For every $q \ge 1$ over any field, the border rank of $\mathrm{CW}_q$ equals $q + 2$: it is a limit of tensors of rank $q + 2$, and no tensor in $(\mathbb{F}^{q+2})^{\otimes 3}$ that is concise (not contained in a smaller subspace in any factor), such as $\mathrm{CW}_q$, has border rank less than $q+2$.

## Proof sketch

The upper bound is the explicit identity

$$
\varepsilon^3 \mathrm{CW}_q = \sum_{i=1}^{q} \varepsilon(x_0 + \varepsilon x_i)(y_0 + \varepsilon y_i)(z_0 + \varepsilon z_i) - \Bigl(x_0 + \varepsilon^2\sum_i x_i\Bigr)\Bigl(y_0 + \varepsilon^2 \sum_i y_i\Bigr)\Bigl(z_0 + \varepsilon^2\sum_i z_i\Bigr) + (1 - q\varepsilon)(x_0 + \varepsilon^3 x_{q+1})(y_0 + \varepsilon^3 y_{q+1})(z_0 + \varepsilon^3 z_{q+1}) + O(\varepsilon^4).
$$

The lower bound holds because border rank of a concise tensor is at least the dimension of each factor, by flattening rank.

## Depends on

- [The Coppersmith–Winograd tensor](cw-tensor.md)

## Sources

- D. Coppersmith, S. Winograd, "Matrix multiplication via arithmetic progressions", Journal of Symbolic Computation 9 (1990) 251-280.
