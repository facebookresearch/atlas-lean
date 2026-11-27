# Uniform exact circuit lower bounds for directed Hamiltonian cycles and permanents

For $m$ vertices let $H_m$ be the formal polynomial $\sum_{\pi}\prod_{i\in[m]} X_{i,\pi(i)}$ with the sum restricted to permutations that are a single spanning cycle. Let $\operatorname{per}_m$ be the same sum over all permutations. These are polynomials in the $m^2$ independent matrix variables. A circuit may share gates and use arbitrary field constants; its size charges the binary addition, subtraction and multiplication gates, not inputs, constants or output selection. It must compute the formal polynomial, not merely its value at field points.

For every natural $q,C$ there exists $N$ such that, for every $m\ge N$ and every field $F$ of characteristic $q$, the minimum size of an exact circuit for $H_m$ is strictly greater than $m^C$. For $q\ne2$, the minimum size for $\operatorname{per}_m$ is also strictly greater than $m^C$, with the same $N$. There is no restriction $C\ge1$ in this statement; it includes characteristic zero, and only the permanent conclusion is restricted in characteristic two.

## Depends on

- The two matrix polynomials and the exact arithmetic circuit cost defined above.

## Proof depends on

- [Exact lower bound for the paired path-count polynomial](paired-count-exact-circuit-lower-bound.md).
- The Hamiltonian-cycle and non-characteristic-two permanent projections with polynomial index growth, padding, and transfer of the lower bound uniformly within each characteristic.

## Expansion

Prove the two algebraic reductions at the level of formal polynomials and separate characteristic descent and padding. The bound does not assert the stronger manuscript bound on approximation of only degree-$m$ coefficients.

## Sources

- OpenAI, [Corollary 1.2](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Computability/VPVNP/Separation.lean#L31-L36), [Directed cycle polynomial](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Computability/VPVNP/Hamiltonian.lean#L108-L111), and [Permanent](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Computability/VPVNP/PermanentPadding.lean#L19-L27).
