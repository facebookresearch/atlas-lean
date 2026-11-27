# Randomized logspace is in deterministic polynomial time

$\mathsf{RL}\subseteq\mathsf{RP}$, $\mathsf{BPL}\subseteq\mathsf{BPP}$, and in fact $\mathsf{BPL}\subseteq\mathsf{P}$ and $\mathsf{RL}\subseteq\mathsf{P}$.

## Proof sketch

The machine has polynomially many configurations; its acceptance probability after $T$ steps is $e_{\text{start}}^{\top}M^T\mathbf{1}_{\text{acc}}$ for the substochastic transition matrix $M$ with entries in $\{0,1/2,1\}$, which is computed exactly by $T$ matrix–vector products with rational entries of polynomially many bits.

## Depends on

- [Randomized logarithmic space RL and BPL](rl-and-bpl.md)
- [The complexity class P](../../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [The class RP](../../../complexity-classes/time-and-space-complexity-classes/rp.md)

## Proof depends on

- [Configuration graph of a space-bounded machine](../../../complexity-classes/space-and-time-complexity/configuration-graph-of-a-space-bounded-machine.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapter 7.
