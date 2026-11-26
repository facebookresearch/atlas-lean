# #P-lowness is exactly UP ∩ coUP

For every language $A$, $\#\mathsf{P}^{A}=\#\mathsf{P}$ if and only if $A\in\mathsf{UP}\cap\mathsf{coUP}$.

## Proof sketch

For $A\in\mathsf{UP}\cap\mathsf{coUP}$, answer each query by guessing the unique certificate of membership or of non-membership, which multiplies the path count by exactly $1$. Conversely, if $\chi_A$ and $\chi_{\overline{A}}$ are $\#\mathsf{P}$ functions then their machines have at most one accepting path, so $A,\overline{A}\in\mathsf{UP}$.

## Depends on

- [GapP and the gap-definable classes SPP, WPP, LWPP, AWPP, C=P and Mod_kP](gap-definable-classes.md)
- [The counting class $\#P$](../../complexity-classes/time-and-space-complexity-classes/sharp-p.md)
- [Unambiguous and few-witness polynomial time: UP and FewP](../../complexity-classes/structural-complexity/reducibilities-and-isomorphism/up-and-fewp.md)

## Sources

- Johannes Köbler, Uwe Schöning, Seinosuke Toda and Jacobo Torán, "Turing Machines with Few Accepting Computations and Low Sets for PP", Journal of Computer and System Sciences 44(2), 1992.
