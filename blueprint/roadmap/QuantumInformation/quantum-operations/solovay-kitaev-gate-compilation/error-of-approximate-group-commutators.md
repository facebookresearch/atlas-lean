# Approximate commutators of near-identity unitaries are quadratically accurate

There is a constant $c'$ such that if $V, W \in \mathrm{SU}(d)$ satisfy $\|V - I\|, \|W - I\| \le r$ and $\tilde V, \tilde W$ satisfy $\|\tilde V - V\|, \|\tilde W - W\| \le \varepsilon$, then

$$
\| \tilde V \tilde W \tilde V^{-1} \tilde W^{-1} - V W V^{-1} W^{-1} \| \le c' (\varepsilon r + \varepsilon^2) .
$$

## Proof sketch

Write $V = I + A$, $\tilde V = V + E$ and similarly for $W$. Expanding the commutator, all terms linear in the errors $E$ that are not multiplied by $A$ or $B$ cancel because $[I, \cdot] = 0$; the remaining linear terms carry a factor of size $r$, and the rest are quadratic in the errors.

## Proof depends on

- [Dense inverse-closed gate sets and epsilon-nets in SU(d)](dense-gate-sets-and-epsilon-nets.md)

## Sources

- Christopher M. Dawson, Michael A. Nielsen, "The Solovay-Kitaev algorithm", Quantum Information and Computation 6(1) (2006); arXiv:quant-ph/0505030.
- Alexei Kitaev, Alexander Shen, Mikhail Vyalyi, "Classical and Quantum Computation", Graduate Studies in Mathematics 47, AMS (2002).
