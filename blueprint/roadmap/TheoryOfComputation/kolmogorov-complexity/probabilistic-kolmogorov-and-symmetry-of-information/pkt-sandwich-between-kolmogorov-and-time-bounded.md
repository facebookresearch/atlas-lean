# Sandwich bounds: K(x) − O(log t) ≤ pK^t(x) ≤ rK^t(x), K^t(x) up to constants and time overhead

There are a constant $c$ and a polynomial $q$ (depending only on $U$) such that for all strings $x,y$ and all $t\ge |x|+|y|$:

1. $\mathrm{pK}^{q(t)}(x\mid y)\le \mathrm{rK}^t(x\mid y)+c$ and $\mathrm{pK}^{q(t)}(x\mid y)\le K^t(x\mid y)+c$;
2. $K(x\mid y)\le \mathrm{pK}^t(x\mid y)+c\log t$, where $K$ is the time-unbounded conditional complexity.

In particular $\mathrm{pK}^t$ is sandwiched between resource-unbounded complexity and the deterministic and randomized time-bounded measures, up to logarithmic additive terms and polynomial time overhead.

## Proof sketch

For the upper bounds, a randomized program can be run deterministically with its coins read from the public string $w$; whenever it succeeds with probability $2/3$ over coins, the same short program succeeds for a $2/3$ fraction of $w$, and a deterministic program simply ignores $w$. For the lower bound, let $k=\mathrm{pK}^t(x\mid y)$; each fixed $w$ yields at most $2^{k+1}$ outputs of programs of length at most $k$, so by averaging the set $S$ of strings printed for at least a $2/3$ fraction of $w$ has size at most $3\cdot 2^{k}$. Given $y$, $k$ and $t$, the set $S$ is computable by exhaustive simulation, so $x$ is described by its index in $S$ together with $O(\log t)$ bits for $k,t$.

## Depends on

- [Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form](pkt-probabilistic-time-bounded-kolmogorov-complexity.md)
- [Kolmogorov complexity](../k.md)

## Proof depends on

- [Few strings have small complexity](../incompressible-strings-and-kolmogorov-complexity/card-lt-two-pow.md)
- [Optimality (the invariance theorem)](../exists-k-le-of-partrec.md)

## Sources

- Halley Goldberg, Valentine Kabanets, Zhenjian Lu and Igor C. Oliveira, "Probabilistic Kolmogorov Complexity with Applications to Average-Case Complexity", CCC (2022), ECCC TR22-072.
- Shuichi Hirahara, Rahul Ilango, Zhenjian Lu, Mikito Nanashima and Igor C. Oliveira, "A Duality Between One-Way Functions and Average-Case Symmetry of Information", STOC (2023), ECCC TR23-035.
