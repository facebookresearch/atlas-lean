# Space-bounded pseudorandom generators with error below 1/2 have stretch below 2^k

If $G : \{0,1\}^k \to \{0,1\}^\ell$ is an $(s, \varepsilon)$-pseudorandom generator against read-once programs of width $2^s$ with $s \ge 1$ and $\varepsilon < 1/2$, then $\ell < 2^k$. The hypothesis $\varepsilon < 1$ printed in Exercise 8.25(2) of Goldreich's 2007 public draft (derived there from Exercises 8.37 and 8.38) does not suffice: $\sigma \mapsto \sigma\sigma$ has $\ell = 2 = 2^1$ and error $1/2$.

## Proof sketch

By the previous theorem $G$ is $2\varepsilon$-biased with $2\varepsilon < 1$, and an $\varepsilon'$-biased sample space with $\varepsilon' < 1$ has fewer output bits than seeds.

## Depends on

- [Read-once branching program and space-bounded pseudorandom generator](../read-once-branching-programs-and-space-bounded-prgs.md)

## Proof depends on

- [Space-bounded pseudorandom generators are small-bias generators](../space-bounded-prgs-are-small-bias.md)
- [Stretch limits for low-degree and linear small-bias generators](../../small-bias-spaces/small-bias-generator-stretch-limits.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercises 8.25(2), 8.37 and 8.38 (numbering of the 2007 public draft).
