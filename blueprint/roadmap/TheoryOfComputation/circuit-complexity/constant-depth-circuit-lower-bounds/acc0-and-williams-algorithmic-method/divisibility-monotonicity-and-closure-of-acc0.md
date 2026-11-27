# Divisibility monotonicity and Boolean closure of ACC0

For moduli $q\mid q'$, a $\mathrm{MOD}_q$ gate is simulated in constant depth by a $\mathrm{MOD}_{q'}$ gate reading each wire $q'/q$ times, so $\mathsf{AC}^0[q]\subseteq\mathsf{AC}^0[q']$. Consequently $\mathsf{ACC}^0=\bigcup_{q\ge2}\mathsf{AC}^0[q]$ is closed under complement, finite union and finite intersection: languages in $\mathsf{AC}^0[q_1]$ and $\mathsf{AC}^0[q_2]$ both lie in $\mathsf{AC}^0[q_1q_2]$.

## Proof sketch

Reading each input $q'/q$ times multiplies the count by $q'/q$, and $q\mid k$ iff $q'\mid (q'/q)k$.

## Depends on

- [The class $\mathsf{ACC}^0$](../../../complexity-classes/time-and-space-complexity-classes/acc0.md)
- [The class $\mathsf{AC}^0(m)$](../../../complexity-classes/time-and-space-complexity-classes/ac0-mod.md)

## Sources

- David A. Barrington, "Bounded-width polynomial-size branching programs recognize exactly those languages in NC^1", Journal of Computer and System Sciences 38(1), 1989.
- Heribert Vollmer, "Introduction to Circuit Complexity: A Uniform Approach", Springer, 1999.
