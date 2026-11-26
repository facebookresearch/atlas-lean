# Hirahara: one-way functions exist iff approximating distributional Kolmogorov complexity is NP-hard and NP is worst-case hard

A reduction to $\mathrm{dK}$ is **parametric honest** if for some constant $\gamma>0$ every query made on inputs of length $n$ has size parameter $s\ge n^{\gamma}$. Assume $\mathsf{NP}\not\subseteq\mathsf{i.o.P/poly}$. Then the following are equivalent:

1. There is a one-way function secure against polynomial-size circuits.
2. For some constant $\epsilon>0$ there is a parametric-honest randomized polynomial-time non-adaptive reduction from $\mathsf{NP}$ to a $(1+\epsilon)$-factor approximation of $\mathrm{dK}^{\tau,A}$, which works for all large polynomials $\tau$ and all oracles $A\in\mathsf{P/poly}$.
3. For some $g(n)=n^{1/(\log\log n)^{O(1)}}$ there is a parametric-honest randomized polynomial-time one-query reduction from $\mathsf{NP}$ to a $g(n)$-factor approximation of $\mathrm{dK}^{\tau,A}$ for all large polynomials $\tau$ and all $A\in\mathsf{P/poly}$.

Since one-way functions imply $\mathsf{NP}\not\subseteq\mathsf{i.o.P/poly}$, unconditionally: a one-way function exists if and only if $\mathsf{NP}\not\subseteq\mathsf{i.o.P/poly}$ and approximating $\mathrm{dK}^{\tau,A}$ is $\mathsf{NP}$-hard in this sense. This is the first characterization of one-way functions by worst-case hardness assumptions, and it excludes errorless Heuristica and error-prone Pessiland simultaneously.

## Proof sketch

For item 1 implies items 2 and 3, a one-way function gives secure computational secret sharing, which turns an instance of Minimum Monotone Satisfying Assignment into a pair $(x,\mathcal D)$ whose distributional complexity is small exactly when the formula has a small satisfying assignment. For the converse, a new theory of P/poly-restricted (mildly black-box) reductions shows that Hirahara's non-black-box worst-case to average-case reduction from NP to avoiding a hitting set generator can be combined with Nanashima's technique: a reduction from NP to $\mathrm{dK}$ yields, in order, a hitting set generator, an auxiliary-input one-way function and, using worst-case hardness of NP together with instance checkability of auxiliary-input one-way functions, a standard one-way function.

## Depends on

- [Distributional Kolmogorov complexity dK^t_λ(x|D) and its probabilistic variant](distributional-kolmogorov-complexity.md)
- [One-way functions exist](../impagliazzo-s-five-worlds/owfexists.md)
- [Heuristica](../impagliazzo-s-five-worlds/heuristica.md)
- [Pessiland](../impagliazzo-s-five-worlds/pessiland.md)
- [Polynomial time with polynomial advice](../../complexity-classes/time-and-space-complexity-classes/ppoly.md)

## Proof depends on

- [Hitting set generators and algorithms that avoid them](hitting-set-generators-and-avoidance.md)
- [Auxiliary-input one-way functions](auxiliary-input-one-way-functions.md)
- [Hirahara: errorless average-case easiness of MINKT yields worst-case additive Õ(√k) approximation of K^t](../../kolmogorov-complexity/probabilistic-kolmogorov-and-symmetry-of-information/hirahara-non-black-box-worst-to-average-minkt.md)

## Sources

- Shuichi Hirahara, "Capturing One-Way Functions via NP-Hardness of Meta-Complexity", STOC (2023), ECCC TR23-037.
