# Quantum Pinsker inequality in nats

For density matrices $\rho,\sigma$ on $\mathbb{C}^\iota$ (possibly singular),

$$
\tfrac12\,\|\rho-\sigma\|_1^2 \le D(\rho\,\|\,\sigma),
$$

with natural logarithms; equivalently $2\,T(\rho,\sigma)^2 \le D(\rho\|\sigma)$. With base-two logarithms the constant becomes $1/(2\ln 2)$.

## Proof sketch

Assume finite divergence and let $d = \|\rho-\sigma\|_1$, attained as $\operatorname{Re}\operatorname{Tr}(U(\rho-\sigma))$ for a unitary $U$. In the resolvent representation insert the test matrix $X = (1-s)I + (1-s)^2 d\,U$; a direct computation bounds the integrand below by $(1-s)d^2$, and integrating over $s\in[0,1]$ gives $d^2/2$.

## Depends on

- [Support inclusion and Umegaki relative entropy](umegaki-relative-entropy.md)
- [Trace norm and trace distance](../density-matrices-and-fidelity/trace-norm-and-trace-distance.md)

## Proof depends on

- [Integral representation of relative entropy by the resolvent kernel](relative-entropy-resolvent-integral.md)
- [Resolvent kernel of quantum relative entropy](relative-entropy-resolvent-kernel.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2):214-253, 2022.
