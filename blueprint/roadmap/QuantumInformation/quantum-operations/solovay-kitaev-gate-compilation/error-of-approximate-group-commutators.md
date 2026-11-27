# Approximate commutators of near-identity unitaries are quadratically accurate

There is a constant $c'$, independent of $d$, such that if $V, W, \tilde V, \tilde W \in \mathrm{SU}(d)$ (operator norm; unitarity of $\tilde V$ and $\tilde W$ is essential) satisfy $\|V - I\|, \|W - I\| \le r$ and $\|\tilde V - V\|, \|\tilde W - W\| \le \varepsilon$, then

$$
\| \tilde V \tilde W \tilde V^{-1} \tilde W^{-1} - V W V^{-1} W^{-1} \| \le c' (\varepsilon r + \varepsilon^2) .
$$

## Proof sketch

Write $V = I + A$, $\tilde V = V + E$ and similarly for $W$; since all four matrices are unitary, $\tilde V^{-1} = \tilde V^{*}$ and $\|\tilde V^{-1} - V^{-1}\| = \|E\| \le \varepsilon$, and all factors have norm $1$. Expanding the commutator, all terms linear in the errors $E$ that are not multiplied by $A$ or $B$ cancel because $[I, \cdot] = 0$; the remaining linear terms carry a factor of size $r$, and the rest are quadratic in the errors. Dawson and Nielsen's explicit bound $8\varepsilon r + 4\varepsilon r^2 + 8\varepsilon^2 + 4\varepsilon^3 + \varepsilon^4$ gives the claim, since $r$ and $\varepsilon$ may be taken at most $2$.

## Proof depends on

- [Dense inverse-closed gate sets and epsilon-nets in SU(d)](dense-gate-sets-and-epsilon-nets.md)

## Sources

- Christopher M. Dawson, Michael A. Nielsen, "The Solovay-Kitaev algorithm", Quantum Information and Computation 6(1) (2006); arXiv:quant-ph/0505030 (Section 4.2, Lemma 1).
- Alexei Kitaev, Alexander Shen, Mikhail Vyalyi, "Classical and Quantum Computation", Graduate Studies in Mathematics 47, AMS (2002).
