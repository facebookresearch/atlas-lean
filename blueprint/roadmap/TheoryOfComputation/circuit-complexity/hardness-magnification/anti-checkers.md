# Anti-checkers

Let $f : \{0,1\}^n \to \{0,1\}$ and $s \ge 1$. A set $Y \subseteq \{0,1\}^n$ is an *anti-checker* for $f$ against circuits of size $s$ if every circuit of size at most $s$ disagrees with $f$ on at least one point of $Y$; equivalently $\mathrm{CC}_Y(f) > s$. Small anti-checkers certify circuit lower bounds by a short list of inputs and their values.

## Depends on

- [Circuit complexity of a Boolean function and truth tables](../minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md)

## Sources

- R. J. Lipton and N. E. Young, "Simple Strategies for Large Zero-Sum Games with Applications to Complexity Theory", STOC 1994.
- I. C. Oliveira, J. Pich and R. Santhanam, "Hardness Magnification near State-Of-The-Art Lower Bounds", Computational Complexity Conference (CCC) 2019.
