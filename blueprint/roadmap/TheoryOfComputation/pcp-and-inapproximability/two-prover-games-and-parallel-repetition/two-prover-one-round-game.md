# Two-prover one-round game and its value

A *two-prover one-round game* $G = (X, Y, A, B, \mu, V)$ consists of finite question sets $X, Y$, finite answer sets $A, B$, a probability distribution $\mu$ on $X \times Y$ and a predicate $V : X \times Y \times A \times B \to \{0,1\}$. The referee draws $(x, y) \sim \mu$, sends $x$ to Alice and $y$ to Bob, receives $a$ and $b$, and accepts iff $V(x, y, a, b) = 1$. The (classical) *value* is

$$\mathrm{val}(G) = \max_{f : X \to A,\ g : Y \to B} \Pr_{(x,y) \sim \mu}\big[V(x, y, f(x), g(y)) = 1\big].$$

Shared randomness does not increase the value, since a randomized strategy is a convex combination of deterministic ones.

## Sources

- T. Holenstein, "Parallel Repetition: Simplifications and the No-Signaling Case", Theory of Computing 5, 2009.
- R. Raz, "A Parallel Repetition Theorem", SIAM Journal on Computing 27(3), 1998.
