# Operator Chernoff bound for binomial tails of an effect

For an element $0\le X\le1$ of a star-ordered algebra (with continuous functional calculus), integers $k\ge1$ and $d\ge0$, let $B_{k,d}(X) = \sum_{j>d}\binom kjX^j(1-X)^{k-j}$, the operator probability of more than $d$ successes in $k$ trials. If $0<\theta<1$ and $2d\le\theta k$, then

$$
1-B_{k,d}(X)\le\frac{1-X}{1-\theta}+e^{-\theta^2k/2},
$$

and consequently for every state $\varphi$ with $\operatorname{Re}\varphi(X)\ge1-\kappa$: $\operatorname{Re}\varphi(B_{k,d}(X))\ge1-\kappa/(1-\theta)-e^{-\theta^2k/2}$. Also $0\le B_{k,d}(X)\le1$.

## Proof sketch

By functional calculus it suffices to prove the scalar inequality on $[0,1]$. For $x\le\theta$ the right side is at least $1$; for $x>\theta$ the mean $kx$ exceeds $\theta k\ge d+\theta k/2$, and Hoeffding's inequality bounds the lower tail by $e^{-2(\theta k/2)^2/k} = e^{-\theta^2k/2}$. Applying the state preserves the order.

## Depends on

- [States on star-ordered algebras, state-dependent norm and approximation](../../../../QuantumInformation/quantum-foundations/states-and-measurements-on-operator-algebras/algebraic-states-and-state-dependent-norm.md)

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "Quantum soundness of the classical low individual degree test", arXiv:2009.12982, 2020.
