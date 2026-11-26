# Mass complexity of a Boolean function

For a Boolean function $f:\{0,1\}^n\to\{0,1\}$ and $k\ge 1$, the *direct product* $f^{\times k}:\{0,1\}^{kn}\to\{0,1\}^k$ evaluates $f$ on $k$ independent input blocks. The *mass complexity* $C(f^{\times k})$ is the least size of a De Morgan circuit (NOT, AND and OR charged one each, constants free) computing $f^{\times k}$. Trivially $C(f^{\times k})\le k\,C(f)$; *mass production* asks when the cost per copy can be much smaller.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Sources

- Dietmar Uhlig, "Networks Computing Boolean Functions for Multiple Input Values", Boolean Function Complexity, 1992.
- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987.
