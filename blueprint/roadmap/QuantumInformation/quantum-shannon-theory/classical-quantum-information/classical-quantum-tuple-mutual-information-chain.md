# Chain rule for the mutual information between classical tuples and a quantum register

Let $X_1,\dots,X_n$ be finite sets (possibly different), $p$ a joint distribution on $X_1\times\dots\times X_n$, and $(\rho_x)$ density matrices on $\mathbb{C}^\iota$ indexed by tuples $x=(x_1,\dots,x_n)$. For the classical-quantum state $\rho_{QX} = \sum_x p(x)\rho_x\otimes|x\rangle\langle x|$,

$$
I(Q : X_1\cdots X_n) = \sum_{i=1}^n \ \mathbb{E}_{x_{< i}\sim p}\Big[\, I(Q:X_i \mid X_{< i}=x_{< i})\,\Big],
$$

where $I(Q:X_i\mid X_{< i} = x_{< i})$ is the mutual information of the classical-quantum state formed by the conditional law of $X_i$ given the prefix $x_{< i}$ and the conditional quantum marginals $\sum_{x_{>i}} p(x_{>i}\mid x_{\le i})\,\rho_x$; prefixes of probability zero contribute zero. For $n=2$ this reads $I(Q:XY) = I(Q:X) + \sum_x p_X(x)\,I(Q:Y\mid X=x)$, and for $n = 0$ both sides are $0$.

## Proof sketch

For two labels, apply the classical-quantum mutual information formula to the pair and to the first label, and the common-reference decomposition with reference equal to the conditional quantum marginal given $x$; the cross terms cancel. Mutual information is invariant under relabelling the classical alphabet by a bijection, so splitting off the first coordinate of a tuple and inducting on the tail gives the general chain rule.

## Depends on

- [Classical-quantum states](classical-quantum-state.md)
- [Quantum mutual information](quantum-mutual-information.md)
- [Chain rule for mutual information](../../../InformationTheory/entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information-chain-rule.md)

## Proof depends on

- [Mutual information of a classical-quantum state](classical-quantum-mutual-information.md)
- [Divergence to a common reference and the product-reference bound](classical-quantum-common-reference-decomposition.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2):214-253, 2022.
