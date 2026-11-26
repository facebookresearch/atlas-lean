# Approximating the entangled value of a nonlocal game is undecidable

There is no algorithm that, given a synchronous two-prover one-round game $G$ promised to satisfy $\omega^*(G) = 1$ or $\omega^*(G) \le 1/2$, decides which case holds. Consequently there is no computable function $D(G)$ such that strategies of local dimension at most $D(G)$ approximate $\omega^*(G)$ to within additive error $1/4$ for every game $G$.

## Proof sketch

A decision procedure for the promise problem would decide the halting problem through $M \mapsto G_M$. If a computable dimension bound $D$ existed, one could approximate $\omega^*(G)$ within $1/4$ by an exhaustive search over a sufficiently fine finite net of strategies of dimension $D(G)$, again deciding the promise problem.

## Depends on

- [Synchronous two-prover games](synchronous-two-prover-games.md)
- [Uniformly generated families of two-prover one-round games](uniformly-generated-game-families.md)

## Proof depends on

- [The halting problem reduces to the entangled value gap problem](halting-problem-reduces-to-entangled-value-gap.md)
- [The halting problem is undecidable by multi-stack machines](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halting.md)

## Sources

- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, Henry Yuen, "MIP* = RE", Communications of the ACM 64(11) (2021); arXiv:2001.04383.
