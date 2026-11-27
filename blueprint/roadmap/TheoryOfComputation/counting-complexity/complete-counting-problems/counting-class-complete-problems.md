# Complete problems for ⊕P, Mod_kP, C=P and US

Under polynomial-time many-one reductions: $\oplus\mathrm{SAT}=\{\varphi:\#\varphi\text{ odd}\}$ is $\oplus\mathsf{P}$-complete; $\mathrm{Mod}_k\mathrm{SAT}=\{\varphi:\#\varphi\not\equiv0\pmod k\}$ is $\mathsf{Mod}_k\mathsf{P}$-complete; $\{(\varphi,k):\#\varphi\ne k\}$ is complete for $\mathsf{coC_{=}P}$ (so exact counting $\#\varphi=k$ is $\mathsf{C_{=}P}$-complete); and Unique-SAT $\{\varphi:\#\varphi=1\}$ is complete for $\mathsf{US}$, the class of languages defined by 'exactly one accepting path'.

## Proof sketch

Each class is defined by a condition on a $\#\mathsf{P}$ function, and the parsimonious Cook–Levin reduction transfers the count exactly, so the same condition on $\#\varphi$ is complete.

## Depends on

- [GapP and the gap-definable classes SPP, WPP, LWPP, AWPP, C=P and Mod_kP](../gap-definable-counting-classes/gap-definable-classes.md)
- [The BP and parity operators on complexity classes](../counting-and-the-polynomial-hierarchy/the-bp-and-parity-operators-on-complexity.md)

## Proof depends on

- [The Cook–Levin reduction is parsimonious](parsimonious-cook-levin.md)

## Sources

- Leslie G. Valiant, "The Complexity of Computing the Permanent", Theoretical Computer Science 8(2), 1979.
- Richard Beigel and John Gill, "Counting Classes: Thresholds, Parity, Mods, and Fewness", Theoretical Computer Science 103(1), 1992.
- Lance Fortnow, "Counting Complexity", Complexity Theory Retrospective II, 1997.
- Andreas Blass and Yuri Gurevich, "On the Unique Satisfiability Problem", Information and Control 55(1–3), 1982 (completeness of Unique-SAT for US).
