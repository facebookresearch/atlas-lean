# Chaitin's halting probability Ω

For a prefix-free description method $M$, *Chaitin's halting probability* is $\Omega_M = \sum_{p \in \mathrm{dom}(M)} 2^{-|p|}$, the probability that $M$ halts on a program given by fair coin flips (read until a halting program is completed). By Kraft's inequality $0 \le \Omega_M \le 1$, and for the universal prefix-free method $0 < \Omega_U < 1$ (some program halts and some program does not).

## Depends on

- [Prefix-free Kolmogorov complexity](prefix-free-kolmogorov-complexity.md)

## Proof depends on

- [Kraft's inequality for prefix codes](../../../InformationTheory/source-coding/kraft-mcmillan-lengths.md)

## Sources

- G. J. Chaitin, "A Theory of Program Size Formally Identical to Information Theory", Journal of the ACM 22(3), 329–340, 1975.
- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
