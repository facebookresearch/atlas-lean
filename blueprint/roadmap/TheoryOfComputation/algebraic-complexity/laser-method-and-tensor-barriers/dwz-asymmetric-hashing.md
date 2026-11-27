# Duan–Wu–Zhou asymmetric hashing and the combination loss

In the recursive laser method on $\mathrm{CW}_q^{\otimes 2^m}$, merging level-$\ell$ constituents into level-$(\ell+1)$ blocks incurs a **combination loss**: the hashing at level $\ell + 1$ forces all three marginals of a block triple to be consistent, so distributions whose $X$-marginal is shared by many distinct constituent distributions lose a factor $2^{N(H(\alpha) - H(\alpha_X))}$. **Asymmetric hashing** imposes the progression-free hashing constraint on one side only and allows collisions on the other two sides to be resolved later at the constituent level. This recovers part of the combination loss and yields a strictly larger lower bound on the value of level-$\ell$ constituents whenever the relevant distribution $\alpha$ is not determined by its marginals. This analysis lies outside the framework covered by the [Ambainis–Filmus–Le Gall limitation](aflg-barrier.md), and with it Duan, Wu and Zhou prove [$\omega < 2.371866$](../matrix-multiplication-exponent/duan-wu-zhou2022-upper.md), below that framework's barrier of $2.3725$.

## Proof sketch

Hash only the $X$-blocks injectively into a progression-free set, so that each surviving $X$-block determines a set of compatible $(Y, Z)$-block pairs; at the next level these partial structures are completed by treating the $Y$ side as the matrix multiplication side and paying for collisions with a counting argument on the joint distribution rather than its marginals.

## Depends on

- [Coppersmith–Winograd hashing with progression-free sets](salem-spencer-hashing.md)
- [The Coppersmith–Winograd tensor](cw-tensor.md)
- [The value of a tensor in the laser method](tensor-value.md)

## Proof depends on

- [The laser method bound on omega from tensor values](laser-method-bound.md)

## Sources

- R. Duan, H. Wu, R. Zhou, "Faster matrix multiplication via asymmetric hashing", FOCS (2023), arXiv:2210.10173.
