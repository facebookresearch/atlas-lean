# Duan–Wu–Zhou: omega < 2.371866, breaking the Coppersmith–Winograd barrier

Analysing the eighth power $\mathrm{CW}_q^{\otimes 8}$ with asymmetric hashing compensates part of the combination loss and yields

$$
\omega < 2.371866,
$$

improving $\omega < 2.372860$. The new analysis of constituent tensors lies outside the framework covered by the Ambainis-Filmus-Le Gall limitation, whose barrier of $2.3725$ is therefore not a barrier for the laser method in general.

## Proof sketch

Combine the refined laser method with asymmetric hashing at each recursion level, solve the resulting nonlinear optimization over distributions on constituents of $\mathrm{CW}_5^{\otimes 8}$ numerically with rigorous verification of the feasible point.

## Depends on

- [Duan–Wu–Zhou asymmetric hashing and the combination loss](dwz-asymmetric-hashing.md)
- [Ambainis–Filmus–Le Gall: limitations of the Coppersmith–Winograd analysis](aflg-barrier.md)
- [Alman–Vassilevska Williams: refined laser method and omega < 2.37286](avw-refined-laser.md)
- [Duan–Wu–Zhou bound on the square exponent](../matrix-multiplication-exponent/duan-wu-zhou2022-upper.md)

## Proof depends on

- [Duan–Wu–Zhou asymmetric hashing and the combination loss](dwz-asymmetric-hashing.md)
- [Ambainis–Filmus–Le Gall: limitations of the Coppersmith–Winograd analysis](aflg-barrier.md)
- [Alman–Vassilevska Williams: refined laser method and omega < 2.37286](avw-refined-laser.md)
- [Duan–Wu–Zhou bound on the square exponent](../matrix-multiplication-exponent/duan-wu-zhou2022-upper.md)

## Sources

- R. Duan, H. Wu, R. Zhou, "Faster matrix multiplication via asymmetric hashing", FOCS (2023), arXiv:2210.10173.
