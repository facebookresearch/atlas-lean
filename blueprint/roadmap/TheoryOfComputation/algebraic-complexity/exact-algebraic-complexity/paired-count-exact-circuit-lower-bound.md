# Uniform exact circuit lower bounds for the paired path-count family

Let $P_n=\sum_x U_n(x)\prod_{i<n}X_{i,x_i}$ over the integers, with $x$ ranging over all length-$n$ bit words. Here $U_n(x)$ is the unsigned coefficient in the [clocked two-tape path counts](clocked-two-tape-path-counts.md), with clock $n^{10^9}$. An exact circuit computes the formal polynomial from free variables and constants, counting binary $+,-,\times$ gates with shared prior results and free output selection. For every natural $C\ge1$ and every natural characteristic $q$, there exists $N$ such that for every $n\ge N$ and every field $F$ of characteristic $q$, the minimum exact circuit size of the coefficient image $P_n^F$ is strictly greater than $n^C$. The threshold can depend on $C,q$ but is chosen before the field. This is formal polynomial equality, including over finite fields, and not a degree-component border bound.

## Depends on

- The unsigned coefficient in the [clocked two-tape path counts](clocked-two-tape-path-counts.md), and the integer paired polynomial and exact $+,-,\times$ circuit conventions above.

## Proof depends on

- The fixed compressed-pair compiler and uniform diagonal argument forcing one eventually superpolynomial size lower bound in each characteristic.

## Expansion

Separate the paired-polynomial convention from the VNP-completeness theorem when building the native model. Isolate a certificate for the fixed pair compiler and the diagonal contradiction; preserve the threshold before quantifying over coefficient fields. The completeness result is not itself a circuit size lower bound.

## Related topics

- [VNP-completeness of the same family](paired-count-vnp-family.md) is a separate result.

## Sources

- OpenAI, [Uniform lower bound and exact separation corollary](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Computability/VPVNP/Separation.lean#L18-L29) and [Minimum formal circuit size](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Computability/VPVNP/CircuitSize.lean#L32-L61).
