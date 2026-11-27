# MOD_q circuits are simulated in AC^1, NC^2 and P/poly

For every $q\ge2$ and $i\ge0$, $\mathsf{AC}^i[q]\subseteq\mathsf{AC}^{i+1}$; in particular $\mathsf{ACC}^0\subseteq\mathsf{AC}^1\subseteq\mathsf{NC}^2\subseteq\mathsf{P}/\mathsf{poly}$. Moreover unbounded-depth circuits with $\mathrm{MOD}_q$ gates of polynomial size have De Morgan circuits of polynomial size.

## Proof sketch

Replace each $\mathrm{MOD}_q$ gate by its majority-based circuit and each majority gate by a logarithmic-depth De Morgan circuit (for the $\mathsf{NC}$ inclusion) or by an $\mathsf{AC}^1$ circuit. A majority gate of polynomial fan-in costs depth $O(\log n)$, so depth $O(\log^i n)$ becomes $O(\log^{i+1} n)$, and polynomial size is preserved.

## Depends on

- [The AC, TC and AC[q] hierarchies](ac-tc-and-acq-hierarchies.md)
- [The class $\mathsf{ACC}^0$](../../complexity-classes/time-and-space-complexity-classes/acc0.md)

## Proof depends on

- [MOD_q gates from majority gates: AC^i[q] is contained in TC^i](mod-q-from-majority-gates.md)
- [Threshold and majority are in NC1](threshold-and-majority-in-nc1.md)

## Sources

- Heribert Vollmer, "Introduction to Circuit Complexity: A Uniform Approach", Springer, 1999.
- Ashok K. Chandra, Larry Stockmeyer, Uzi Vishkin, "Constant Depth Reducibility", SIAM Journal on Computing, 1984.
