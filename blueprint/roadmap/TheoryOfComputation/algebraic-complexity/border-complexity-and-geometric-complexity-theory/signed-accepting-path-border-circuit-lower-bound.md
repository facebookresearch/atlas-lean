# Degree-component border lower bound for the signed path-count polynomial

Use paired variables $X_{i,b}$ at positions $i\in[n]$ and bits $b\in\{0,1\}$. For each bit word $x$ of length $n$, take the signed coefficient $U_n^\star(x)$ from the [clocked two-tape path counts](../exact-algebraic-complexity/clocked-two-tape-path-counts.md), with clock $n^{100}$. The integer polynomial $P_n^\star$ sums this coefficient times $\prod_i X_{i,x_i}$ over the bit words. This signed family is not the unsigned accepting-path family.

There is an absolute real $c>0$ such that for each natural characteristic $q$ there is $N$ such that, for all $n\ge N$ and all fields $F$ of characteristic $q$, the degree-$n$ [degree-component border size](degree-component-border-circuits.md) of $P_n^\star$ specialized to $F$ is at least

$$
2^{c(\log_2 n)^{5/4}}.
$$

The threshold is uniform across fields of the chosen characteristic. Both the target and the approximating circuit outputs are interpreted by formal polynomial coefficients. The bound implies the same lower bound for ordinary exact circuits, by inclusion of attainable vectors in their closure; it is not the sharper bound for approximating Hamiltonian cycle or permanent.

## Depends on

- The signed coefficient in the [clocked two-tape path counts](../exact-algebraic-complexity/clocked-two-tape-path-counts.md) and the [degree-component border size](degree-component-border-circuits.md).

## Proof depends on

- Uniform transfer from characteristic zero and positive prime fields, using the charged native-column stretch constructions and the absolute-rate crossing estimate.

## Expansion

Port the signed decoder/clock and its coefficient specialization without silently replacing signed paths by acceptance counts. Isolate the priced shortening and stretch hypotheses and their proofs over the prime fields before applying the uniform transfer. Keep the base-two logarithm, degree projection and non-strict bound.

## Sources

- OpenAI, [Uniform transfer with its explicit premises](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Computability/BorderVNP/RateCrossing.lean#L66-L77), [Prime-field stretch proofs discharging those premises](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Computability/BorderVNP/DiagonalPaidColumns.lean#L43-L67), [The rate](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Computability/BorderVNP/TransferRate.lean#L18-L25), and [Signed polynomial](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Computability/BorderVNP/SignedFamily.lean#L15-L30).
