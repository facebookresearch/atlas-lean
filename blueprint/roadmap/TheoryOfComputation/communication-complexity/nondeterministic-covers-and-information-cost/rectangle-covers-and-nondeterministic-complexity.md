# Rectangle covers and nondeterministic communication complexity

For $f : X \times Y \to \{0,1\}$ and $z \in \{0,1\}$, a *$z$-cover* of $f$ is a family of rectangles contained in $f^{-1}(z)$ whose union is $f^{-1}(z)$; the *cover number* $C^z(f)$ is the least size of a $z$-cover. The *nondeterministic communication complexity* $N^z(f)$ is the least $k \in \mathbb{N}$ such that $f$ has a $z$-cover by at most $2^k$ rectangles, i.e. $N^z(f) = \lceil \log_2 \max(1, C^z(f)) \rceil$; if $f$ never takes the value $z$, the empty family is a $z$-cover, $C^z(f) = 0$ and $N^z(f) = 0$. it is the cost of protocols in which the players receive a common guess and accept iff the guessed rectangle contains their input. For partial functions or relations the rectangles may contain "don't care" pairs. Always $N^z(f) \le D(f)$.

## Depends on

- [Deterministic two-party protocol](../deterministic-communication-protocols/protocol.md)
- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)
- [Fooling set](../deterministic-communication-protocols/is-fooling-set.md)

## Sources

- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
