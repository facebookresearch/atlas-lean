# The Karchmer–Wigderson game of a Boolean function

For a Boolean function $f:\{0,1\}^n\to\{0,1\}$, the *Karchmer–Wigderson game* $\mathrm{KW}_f$ is the communication search problem in which Alice receives $x\in f^{-1}(1)$, Bob receives $y\in f^{-1}(0)$, and they must agree on an index $i$ with $x_i\neq y_i$. In the *monotone* game $\mathrm{KW}^+_f$ for monotone $f$, they must find $i$ with $x_i=1$ and $y_i=0$. The *communication complexity* $\mathrm{CC}(\mathrm{KW}_f)$ is the least depth of a deterministic protocol tree solving the game.

## Depends on

- [Communication cost of a protocol](../../../../communication-complexity/deterministic-communication-protocols/depth.md)
- [Rectangle lemma](../../../../communication-complexity/deterministic-communication-protocols/transcript-eq-iff.md)

## Sources

- Mauricio Karchmer, Avi Wigderson, "Monotone circuits for connectivity require super-logarithmic depth", SIAM Journal on Discrete Mathematics, 1990.
- Eyal Kushilevitz, Noam Nisan, "Communication Complexity", Cambridge University Press, 1997.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
