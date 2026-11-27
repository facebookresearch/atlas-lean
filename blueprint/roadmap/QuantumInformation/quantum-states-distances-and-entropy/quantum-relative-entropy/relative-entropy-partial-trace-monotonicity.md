# Monotonicity of quantum relative entropy under partial trace

For positive semidefinite $\rho,\sigma$ on $\mathbb{C}^\iota\otimes\mathbb{C}^\kappa$ (not necessarily normalized, possibly singular),

$$
D(\operatorname{Tr}_\kappa\rho\,\|\,\operatorname{Tr}_\kappa\sigma) \le D(\rho\,\|\,\sigma) \quad\text{and}\quad D(\operatorname{Tr}_\iota\rho\,\|\,\operatorname{Tr}_\iota\sigma) \le D(\rho\,\|\,\sigma),
$$

with natural logarithms and extended values.

## Proof sketch

Support inclusion passes to the reduced matrices. For the resolvent kernel, the test matrix $X\otimes I$ for the joint pair has the same objective value as $X$ for the reduced pair, so the reduced kernel is at most the joint kernel at every $t$. The traces agree, and integrating with the resolvent representation gives the inequality; the other partial trace follows by swapping factors.

## Depends on

- [Support inclusion and Umegaki relative entropy](umegaki-relative-entropy.md)
- [Partial trace over the first factor](../../../LinearAlgebra/linear-maps-and-duality/partial-trace/partial-trace-left.md)
- [Partial trace over the second factor](../../../LinearAlgebra/linear-maps-and-duality/partial-trace/partial-trace-right.md)

## Proof depends on

- [Integral representation of relative entropy by the resolvent kernel](relative-entropy-resolvent-integral.md)
- [Resolvent kernel of quantum relative entropy](relative-entropy-resolvent-kernel.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2):214-253, 2022.
- M. B. Ruskai, "Another short and elementary proof of strong subadditivity of quantum entropy", Reports on Mathematical Physics 60(1):1-12, 2007.
