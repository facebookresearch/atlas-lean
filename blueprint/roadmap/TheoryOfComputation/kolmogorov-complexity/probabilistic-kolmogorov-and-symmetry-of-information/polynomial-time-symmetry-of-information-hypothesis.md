# Polynomial-time symmetry of information hypothesis for K^t and pK^t

For a complexity measure $\mu^t\in\{K^t,\mathrm{pK}^t\}$, **polynomial-time symmetry of information (SoI) for $\mu$** is the hypothesis that there exist a polynomial $p$ and a constant $c$ such that for all strings $x,y$ and all $t\ge |x|+|y|$:

$$
\mu^{p(t)}(x\mid y)+\mu^{p(t)}(y)\ \le\ \mu^{t}(x,y)+c\log t .
$$

The reverse inequality $\mu^{p(t)}(x,y)\le \mu^t(y)+\mu^t(x\mid y)+c\log t$ holds unconditionally, by concatenating self-delimiting descriptions. For time-unbounded Kolmogorov complexity the analogue holds with additive $O(\log(|x|+|y|))$ error (Kolmogorov and Levin), mirroring the identity $I(X;Y)=I(Y;X)$ for Shannon information; the polynomial-time version is stated here as a hypothesis.

## Depends on

- [Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form](pkt-probabilistic-time-bounded-kolmogorov-complexity.md)
- [Kolmogorov complexity](../k.md)
- [Symmetry of mutual information](../../../InformationTheory/information-inequalities/data-processing-inequality/measure-mutual-information-map-swap.md)

## Sources

- Luc Longpré and Osamu Watanabe, "On symmetry of information and polynomial time invertibility", Information and Computation 121(1) (1995).
- Shuichi Hirahara, Rahul Ilango, Zhenjian Lu, Mikito Nanashima and Igor C. Oliveira, "A Duality Between One-Way Functions and Average-Case Symmetry of Information", STOC (2023), ECCC TR23-035.
