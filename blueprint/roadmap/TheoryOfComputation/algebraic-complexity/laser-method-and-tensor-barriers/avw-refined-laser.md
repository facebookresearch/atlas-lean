# Alman–Vassilevska Williams: refined laser method and omega < 2.37286

In the laser method, suppose that after hashing and zeroing out, a direct sum of $B$ subtensors consistent with the target distribution $\alpha$ remains together with $m \cdot B$ further subtensors consistent with other distributions having the same marginals as $\alpha$. Then a random choice of about $B/\sqrt{m}$ of the $\alpha$-consistent subtensors, followed by zeroing out every variable none of them uses, leaves with positive probability a direct sum of $B/\Theta(\sqrt{m})$ independent $\alpha$-consistent subtensors, where the earlier greedy argument kept only $B/\Theta(m)$. This raises the value bound by a factor $\Theta(\sqrt{m})$ whenever $m \gg 1$, and applied to $\mathrm{CW}_5^{\otimes 32}$ it gives the bound $\omega < 2.37286$.

## Proof sketch

In the greedy argument, each $\alpha$-consistent subtensor that is kept forces about $m$ inconsistent subtensors to be zeroed out, and with them about $m$ other $\alpha$-consistent ones. In the refined argument, choose a random set of about $B/\sqrt{m}$ of the $\alpha$-consistent subtensors and zero out every variable none of them uses. An inconsistent subtensor survives only if all of its variable blocks are used by chosen subtensors; the structure of distributions with equal marginals makes this unlikely enough that, with positive probability, every inconsistent subtensor is zeroed out while the chosen consistent ones form a direct sum.

## Depends on

- [The Coppersmith–Winograd tensor](cw-tensor.md)
- [The value of a tensor in the laser method](tensor-value.md)

## Proof depends on

- [The laser method bound on omega from tensor values](laser-method-bound.md)
- [Alman–Vassilevska Williams 2020 bound on the square exponent](../matrix-multiplication-exponent/alman-vassilevska-williams2020-upper.md)

## Sources

- J. Alman, V. Vassilevska Williams, "A refined laser method and faster matrix multiplication", SODA (2021), arXiv:2010.05846.
