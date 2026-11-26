# Mild average-case hardness of time-bounded Kolmogorov complexity

$K^t$ is *mildly hard on average* if there is a polynomial $p$ such that every probabilistic polynomial-time heuristic $H$, for all large $n$, errs on a noticeable fraction of inputs:

$$\Pr_{x \leftarrow \{0,1\}^n,\ \text{coins}}\bigl[H(x) \ne K^t(x)\bigr] \ge \frac{1}{p(n)}.$$

## Depends on

- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)
- [Probabilistic polynomial-time Turing machines](../../../ComputerScience/cryptography/security-games/asymptotic-security/probabilistic-polynomial-time-turing-machines.md)

## Sources

- Y. Liu and R. Pass, "On One-way Functions and Kolmogorov Complexity", Proceedings of the 61st Annual IEEE Symposium on Foundations of Computer Science (FOCS), 2020.
