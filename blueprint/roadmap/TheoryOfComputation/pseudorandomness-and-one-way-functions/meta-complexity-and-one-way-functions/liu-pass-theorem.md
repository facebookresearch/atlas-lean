# Liu–Pass: one-way functions exist iff time-bounded Kolmogorov complexity is mildly hard on average

The following are equivalent: (a) one-way functions exist; (b) for some polynomial $t$ with $t(n) > (1+\varepsilon)n$ for a constant $\varepsilon > 0$, $K^t$ is mildly hard on average with respect to the uniform distribution; (c) for every polynomial $t$ with $t(n) > (1+\varepsilon)n$ for a constant $\varepsilon > 0$, $K^t$ is mildly hard on average.

## Proof sketch

For (a) implies (c): from a one-way function build a pseudorandom generator; strings in its image have $K^t$ well below their length while uniform strings do not, so an accurate heuristic for $K^t$ distinguishes the generator. For (b) implies (a): the function mapping $(\ell, \Pi)$ to $(\ell, U^t(\Pi_{1..\ell}))$ is weakly one-way, since an inverter would yield a heuristic computing $K^t$ on most inputs; Yao's amplification makes it strongly one-way.

## Depends on

- [Mild average-case hardness of time-bounded Kolmogorov complexity](mild-average-case-hardness-of-kt.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Proof depends on

- [Yao's amplification: weak one-way functions yield strong one-way functions](../one-way-function-transformations/yao-weak-to-strong-amplification.md)
- [Pseudorandom generators exist if and only if one-way functions exist](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-generators/pseudorandom-generators-exist-if-and-only-if.md)

## Sources

- Y. Liu and R. Pass, "On One-way Functions and Kolmogorov Complexity", Proceedings of the 61st Annual IEEE Symposium on Foundations of Computer Science (FOCS), 2020.
