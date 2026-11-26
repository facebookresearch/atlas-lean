# Balanced group commutator decomposition near the identity

There is a constant $c$ such that for every $U \in \mathrm{SU}(2)$ with $\|U - I\| \le \delta$ (for $\delta$ small enough) there exist $V, W \in \mathrm{SU}(2)$ with $\|V - I\|, \|W - I\| \le c\sqrt{\delta}$ and $U = V W V^{-1} W^{-1}$.

## Proof sketch

Write $U$ as a rotation by angle $\theta = O(\delta)$ about some axis. Choose $V$ and $W$ as rotations by the same angle $\phi$ about perpendicular axes; their commutator is a rotation by angle $\theta'(\phi)$ with $\sin(\theta'/2) = 2\sin^2(\phi/2)\sqrt{1 - \sin^4(\phi/2)}$, so $\phi = O(\sqrt{\theta})$ solves $\theta' = \theta$. Conjugating by a rotation aligns the commutator axis with that of $U$.

## Proof depends on

- [Dense inverse-closed gate sets and epsilon-nets in SU(d)](dense-gate-sets-and-epsilon-nets.md)

## Sources

- Christopher M. Dawson, Michael A. Nielsen, "The Solovay-Kitaev algorithm", Quantum Information and Computation 6(1) (2006); arXiv:quant-ph/0505030.
