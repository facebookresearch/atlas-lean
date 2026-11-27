# Håstad's noisy 3-bit linear test on a projection

Let $\pi : \beta \to \gamma$ and let $A : \{\pm1\}^\gamma \to \{\pm 1\}$ and $B : \{\pm1\}^\beta \to \{\pm1\}$ be folded tables (supposed long codes of labels $c \in \gamma$ and $b \in \beta$ with $\pi(b) = c$). For a noise rate $\delta \in (0, 1/2)$, the test draws $f \in \{\pm1\}^\gamma$ and $g \in \{\pm1\}^\beta$ uniformly and $\mu \in \{\pm1\}^\beta$ with independent coordinates equal to $-1$ with probability $\delta$, and accepts iff

$$A(f)\, B(g)\, B\big((f \circ \pi)\, g\, \mu\big) = 1,$$

products being pointwise. It reads three bits and checks one linear equation over $\mathbb{F}_2$.

## Depends on

- [Long code and folded tables](long-code-and-folded-tables.md)
- [Label Cover (projection games)](../two-prover-games-and-parallel-repetition/label-cover-projection-games.md)

## Sources

- J. Håstad, "Some Optimal Inapproximability Results", Journal of the ACM 48(4), 2001.
