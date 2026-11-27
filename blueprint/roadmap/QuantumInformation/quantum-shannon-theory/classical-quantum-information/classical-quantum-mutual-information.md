# Mutual information of a classical-quantum state

For a classical-quantum state $\rho_{QX} = \sum_x p(x)\rho_x\otimes|x\rangle\langle x|$ with average state $\bar\rho = \sum_x p(x)\rho_x$,

$$
I(Q:X)_\rho = \sum_x p(x)\, D(\rho_x\,\|\,\bar\rho),
$$

in nats; every term with $p(x) > 0$ is finite because $\operatorname{supp}\rho_x\subseteq\operatorname{supp}\bar\rho$. A deterministic label carries no information: if $p$ is a point mass then $I(Q:X) = 0$.

## Proof sketch

The product of the marginals $\bar\rho\otimes\operatorname{diag}(p)$ is itself a classical-quantum state with weights $p$ and constant blocks $\bar\rho$. Applying the chain rule with $q = p$ gives $D_{\mathrm{KL}}(p\|p) = 0$ plus the weighted conditional divergences from $\bar\rho$.

## Depends on

- [Classical-quantum states](classical-quantum-state.md)
- [Quantum mutual information](quantum-mutual-information.md)
- [Support inclusion and Umegaki relative entropy](../../quantum-states-distances-and-entropy/quantum-relative-entropy/umegaki-relative-entropy.md)

## Proof depends on

- [Relative-entropy chain rule for classical-quantum states](classical-quantum-relative-entropy-chain-rule.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2):214-253, 2022.
