# Duan–Wu–Zhou asymmetric hashing and the combination loss

In the recursive laser method on $\mathrm{CW}_q^{\otimes 2^m}$, merging level-$\ell$ constituents into level-$(\ell+1)$ blocks incurs a **combination loss**: when standard symmetric hashing keeps only level-1 $Z$-blocks satisfying the separate split parameters ($2\lambda$ on $S_{0,2,2} \cup S_{2,0,2}$ and $2\mu$ on $S_{1,1,2}$, giving set $Z^M$) instead of the larger set $Z'$ satisfying only the averaged split parameter $2p$ on $S_2$, it loses the ratio $|Z'|/|Z^M|$ (whose exponential rate is governed by the difference between $h(2p)|S_2|$ and $h(2\lambda)|S_{0,2,2} \cup S_{2,0,2}| + h(2\mu)|S_{1,1,2}|$ whenever $\lambda \ne \mu$). **Asymmetric hashing** still applies Salem–Spencer progression-free hashing to all three sides ($X$, $Y$, and $Z$), keeping $X$- and $Y$-blocks unique in surviving triples while allowing $Z$-blocks to be shared across multiple surviving triples (with $Z$-side collisions resolved via the lower-level asymmetric analysis). At the parameters analyzed by Duan, Wu and Zhou (where $\lambda \ne \mu$), this recovers part of the combination loss and yields strictly better value bounds, improving the second-power analysis of $\mathrm{CW}_q^{\otimes 2}$ to $\omega < 2.374631$ (Duan–Wu–Zhou, §4) and the higher-power analysis of $\mathrm{CW}_5$ to [$\omega < 2.371866$](../matrix-multiplication-exponent/duan-wu-zhou2022-upper.md). For $\mathrm{CW}_5$, this analysis escapes the recursive-framework barrier of $2.3725$ in the [Ambainis–Filmus–Le Gall limitation](aflg-barrier.md), while remaining subject to its broader merging barrier of $2.3078$.

## Proof sketch

Apply Salem–Spencer progression-free hashing to all three block families ($X$, $Y$, and $Z$), choosing the modulus so that colliding $X$-blocks and colliding $Y$-blocks are pruned away while $Z$-blocks remain shared among compatible surviving triples (Duan–Wu–Zhou §§2.3, 3.10, Lemma 3.11). Because the level-1 $Z$-blocks are no longer forced to obey the separate per-constituent split counts before hashing, the surviving shared $Z$-blocks capture part of the $|Z'|/|Z^M|$ combination loss, and a hole-fixing and counting argument converts the resulting $Z$-shared subtensor into an improved value bound for the constituent powers.

## Depends on

- [Coppersmith–Winograd hashing with progression-free sets](salem-spencer-hashing.md)
- [The Coppersmith–Winograd tensor](cw-tensor.md)
- [The value of a tensor in the laser method](tensor-value.md)

## Proof depends on

- [The laser method bound on omega from tensor values](laser-method-bound.md)

## Sources

- R. Duan, H. Wu, R. Zhou, "Faster matrix multiplication via asymmetric hashing", FOCS (2023), arXiv:2210.10173.
