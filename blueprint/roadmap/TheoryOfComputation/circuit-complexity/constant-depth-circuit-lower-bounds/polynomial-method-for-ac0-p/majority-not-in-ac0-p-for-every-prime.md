# Majority is not in AC0[p] for any prime p, so AC0[p] is strictly contained in TC0

For every prime $p$, majority is not in $\mathsf{AC}^0[p]$. Since $\mathsf{AC}^0[p]\subseteq\mathsf{TC}^0$ and majority lies in $\mathsf{TC}^0$, one has $\mathsf{AC}^0[p]\subsetneq\mathsf{TC}^0$.

## Proof sketch

Constant-depth circuits for majority give constant-depth circuits for every threshold, every exact-weight function and parity. For odd $p$ this contradicts Smolensky's theorem that parity is not in $\mathsf{AC}^0[p]$; for $p=2$ it contradicts the lower bound for the middle slice, an exact-weight function (equivalently, the case $p=2$ is Razborov's theorem that majority is not in $\mathsf{AC}^0[2]$).

## Depends on

- [The AC, TC and AC[q] hierarchies](../../parallel-circuit-hierarchies/ac-tc-and-acq-hierarchies.md)
- [The majority language](../../../complexity-classes/time-and-space-complexity-classes/majority-dec.md)

## Proof depends on

- [MOD_q gates from majority gates: AC^i[q] is contained in TC^i](../../parallel-circuit-hierarchies/mod-q-from-majority-gates.md)
- [Smolensky's theorem: MOD_q is not in AC0[p]](../smolensky-s-theorem-mod-q-is-not-in-ac0-p.md)
- [Razborov's rank method: the middle slice is not in AC0[2]](middle-slice-not-in-ac0-2.md)
- [Razborov: majority is not in AC0[mod 2]](../../razborov-majority-not-in-ac0-mod-two.md)

## Sources

- Roman Smolensky, "Algebraic Methods in the Theory of Lower Bounds for Boolean Circuit Complexity", Proceedings of the 19th Annual ACM Symposium on Theory of Computing (STOC 1987), 1987.
- Alexander A. Razborov, "Lower Bounds on the Size of Bounded Depth Circuits over a Complete Basis with Logical Addition", Mathematical Notes of the Academy of Sciences of the USSR 41(4), 1987.
