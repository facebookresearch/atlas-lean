# An explicit paired-variable VNP-complete family

For $n\in\mathbb N$ use variables $X_{i,b}$ for $i\in[n]=\{0,\ldots,n-1\}$ and $b\in\{0,1\}$. For each length-$n$ bit word $x$, take the unsigned coefficient $U_n(x)$ from the [clocked two-tape path counts](clocked-two-tape-path-counts.md), with clock $n^{10^9}$. The integer polynomial is $P_n=\sum_x U_n(x)\prod_i X_{i,x_i}$. Let $P_n^F$ be its coefficient image in a field $F$.

Over every field $F$, at every index $n$ the variable type has cardinality $2n$, the polynomial $P_n^F$ is homogeneous of degree $n$, its total degree equals $n$, and the degree in each variable is at most one. The family is in exact $\mathsf{VNP}_F$, and every exact $\mathsf{VNP}_F$ family $f_n$ on varying finite variable types is a polynomial projection of it. This means there is a polynomially bounded index function $r(n)$ (not necessarily monotone), and at each $n$ a substitution of each variable of $P^F_{r(n)}$ by a variable of $f_n$ or a constant in $F$, giving $f_n$ as a formal polynomial.

Here polynomial bounds mean $A n^d$ beyond a threshold. Exact $\mathsf{VP}_F$ requires polynomial bounds on arity, degree and minimum exact circuit size. Circuit size charges each binary $+,-,\times$ gate on constants, variables or earlier results; inputs/constants and selection of an available output do not add gates. Exact $\mathsf{VNP}_F$ also bounds the target arity and degree, and sums one exact VP verifier over all Boolean assignments to a polynomially bounded finite witness type while leaving the target variables formal.

## Depends on

- The unsigned coefficient in the [clocked two-tape path counts](clocked-two-tape-path-counts.md), and the formal circuit size, Boolean verifier sums and polynomial projections specified above.

## Proof depends on

- The clocked interpreter's unique accepting witness encoding and polynomial-size verifier, and the polynomial projection of arbitrary bounded-degree VNP families to the paired coefficient family.

## Expansion

Define the finite-word decoder and nondeterministic machine before using its path count as a polynomial coefficient. Preserve malformed-input handling and exact witness padding. For positive $n$, the all-false word contributes the coefficient $1$, which survives every field specialization and witnesses total degree $n$. Bound reindexing and literal substitutions separately from the lower bound on this family.

## Related topics

- [Exact VP–VNP predicate inequality on paired variables](exact-vp-ne-vnp-on-two-n-variables.md) does not name a separating witness or prove completeness.

## Sources

- OpenAI, [Complete family and all structural claims](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Computability/VPVNP/FamilyResult.lean#L9-L25), [Paired polynomial and specialization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Computability/VPVNP/PairedFamily.lean#L22-L101), [Clocked decoding and accepting count](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Computability/VPVNP/UniversalMachine.lean#L152-L263), and [Exact classes and projections](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Computability/VPVNP/Classes.lean#L18-L65).
