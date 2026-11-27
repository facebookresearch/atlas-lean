# Ω is left-c.e., Martin-Löf random and has only finitely many provable bits

For the universal prefix-free method $U$: (1) $\Omega_U$ is left-computably enumerable: there is a computable increasing sequence of rationals converging to it; (2) its binary expansion $\omega$ satisfies $K(\omega_1 \cdots \omega_n) \ge n - c$ for a constant $c$ and all $n$, so $\Omega_U$ is Martin-Löf random; (3) knowing the first $n$ bits of $\Omega_U$ decides the halting problem for programs of length at most $n$; (4) for every sound computably axiomatized theory there is $N$ such that the theory determines at most $N$ bits of $\Omega_U$.

## Proof sketch

Enumerate halting programs to approximate $\Omega$ from below. Given $\omega_1 \cdots \omega_n$, wait until the approximation exceeds $0.\omega_1\cdots\omega_n$; every program of length at most $n$ that halts has halted by then, and the output can be chosen to be a string of complexity greater than $n$, which forces $K(\omega_1\cdots\omega_n) \ge n - O(1)$. Provability of many bits would similarly give short descriptions of complex strings.

## Depends on

- [Chaitin's halting probability Ω](chaitins-halting-probability.md)
- [Martin-Löf tests and Martin-Löf randomness](martin-lof-tests-and-randomness.md)
- [Prefix-free Kolmogorov complexity](prefix-free-kolmogorov-complexity.md)

## Proof depends on

- [Levin–Schnorr theorem and equivalence with Solovay randomness](levin-schnorr-theorem.md)

## Sources

- G. J. Chaitin, "A Theory of Program Size Formally Identical to Information Theory", Journal of the ACM 22(3), 329–340, 1975.
- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
- A. Shen, V. A. Uspensky and N. Vereshchagin, "Kolmogorov Complexity and Algorithmic Randomness", American Mathematical Society, 2017.
