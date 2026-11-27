# Space-bounded pseudorandom generators with error below 1/2 have stretch below 2^k

If $G : \{0,1\}^k \to \{0,1\}^\ell$ is an $(s, \varepsilon)$-pseudorandom generator against read-once programs of width $2^s$ with $s \ge 1$ and $\varepsilon < 1/2$, then $\ell < 2^k$. The hypothesis $\varepsilon < 1$ printed in Goldreich's Exercise 8.25(2) does not suffice: $\sigma \mapsto \sigma\sigma$ has $\ell = 2 = 2^1$ and error $1/2$.

## Proof sketch

By the previous theorem $G$ is $2\varepsilon$-biased with $2\varepsilon < 1$, and an $\varepsilon'$-biased sample space with $\varepsilon' < 1$ has fewer output bits than seeds.

## Depends on

- [Read-once branching program and space-bounded pseudorandom generator](../space-bounded-and-small-bias-generators/read-once-branching-programs-and-space-bounded-prgs.md)

## Proof depends on

- [Space-bounded pseudorandom generators are small-bias generators](../space-bounded-and-small-bias-generators/space-bounded-prgs-are-small-bias.md)
- [Stretch limits for low-degree and linear small-bias generators](../small-bias-spaces/small-bias-generator-stretch-limits.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", public draft of Chapters 7–8, March 2007.
