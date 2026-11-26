# Fenner–Fortnow–Kurtz: GapP-lowness characterizes SPP

For every language $A$: $\mathsf{GapP}^{A}=\mathsf{GapP}$ if and only if $A\in\mathsf{SPP}$, and $\mathsf{SPP}^{A}=\mathsf{SPP}$ if and only if $A\in\mathsf{SPP}$. Consequently $\mathsf{SPP}$ is low for $\mathsf{LWPP}$ and for $\mathsf{WPP}$: $\mathsf{LWPP}^{\mathsf{SPP}}=\mathsf{LWPP}$ and $\mathsf{WPP}^{\mathsf{SPP}}=\mathsf{WPP}$, and $\mathsf{FewP}\subseteq\mathsf{SPP}$, so $\mathsf{FewP}$ is low for $\mathsf{SPP}$ and $\mathsf{GapP}$.

## Proof sketch

For $A\in\mathsf{SPP}$, replace each oracle query by a guessed answer weighted by the SPP gap of the query (which is $1$ for the true answer and $0$ for the wrong one), multiplying gaps along a path; adaptive queries multiply polynomially many such factors, which stays in $\mathsf{GapP}$. Conversely, $\chi_A\in\mathsf{GapP}^A=\mathsf{GapP}$ shows $A\in\mathsf{SPP}$.

## Depends on

- [GapP and the gap-definable classes SPP, WPP, LWPP, AWPP, C=P and Mod_kP](gap-definable-classes.md)
- [Polynomial time with an oracle](../../complexity-classes/time-and-space-complexity-classes/pwith-oracle.md)

## Proof depends on

- [Closure properties of GapP](gapp-closure.md)

## Sources

- Stephen A. Fenner, Lance J. Fortnow and Stuart A. Kurtz, "Gap-Definable Counting Classes", Journal of Computer and System Sciences 48(1), 1994, Section 5.
