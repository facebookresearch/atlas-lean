# Open ball in a pseudometric space

Let $X$ be a pseudometric space, with distance $d\colon X \times X \to \mathbb{R}$: $d(x, x) = 0$, $d(x, y) = d(y, x)$ and $d(x, z) \le d(x, y) + d(y, z)$ for all $x, y, z \in X$, so that $d \ge 0$, but distinct points may be at distance $0$. Every metric space is a pseudometric space. For $x \in X$ and a real number $r$, the *open ball* of radius $r$ centred at $x$ is the set $B(x, r) = \{y \in X : d(y, x) < r\}$. Any real radius is allowed, and $B(x, r)$ is empty when $r \le 0$. Since $d$ is symmetric, $B(x, r) = \{y \in X : d(x, y) < r\}$.

## Sources

- James R. Munkres, Topology, 2nd ed., Prentice Hall, 2000.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the open ball of any real radius in a pseudometric space: `Metric.ball`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L170 and https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L365-L370.
