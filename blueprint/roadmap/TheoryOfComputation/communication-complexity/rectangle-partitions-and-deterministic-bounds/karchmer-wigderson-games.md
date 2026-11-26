# Karchmer–Wigderson games

For a Boolean function $f : \{0,1\}^n \to \{0,1\}$, the *Karchmer–Wigderson game* $\mathrm{KW}_f$ is the search problem in which Alice holds $x \in f^{-1}(1)$, Bob holds $y \in f^{-1}(0)$, and they must output a coordinate $i$ with $x_i \ne y_i$. For monotone $f$, the *monotone game* $\mathrm{KW}^+_f$ requires a coordinate with $x_i = 1$ and $y_i = 0$, which exists by monotonicity. The Karchmer–Wigderson theorem states that the deterministic communication complexity of $\mathrm{KW}_f$ equals the minimum depth of a De Morgan formula for $f$, and that of $\mathrm{KW}^+_f$ equals the minimum depth of a monotone formula.

## Depends on

- [Deterministic two-party protocol](../deterministic-communication-protocols/protocol.md)
- [Boolean gates](../../circuit-complexity/boolean-circuits/boolean-gate.md)

## Sources

- M. Karchmer and A. Wigderson, "Monotone Circuits for Connectivity Require Super-Logarithmic Depth", SIAM Journal on Discrete Mathematics 3(2), 1990.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
