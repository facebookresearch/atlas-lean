# Fenner–Fortnow–Kurtz: GapP-lowness characterizes SPP

For every language $A$: $\mathsf{GapP}^{A}=\mathsf{GapP}$ if and only if $A\in\mathsf{SPP}$, and $\mathsf{SPP}^{A}=\mathsf{SPP}$ if and only if $A\in\mathsf{SPP}$. Moreover $\mathsf{SPP}$ is low for every uniformly gap-definable class (such as $\mathsf{PP}$, $\mathsf{C_{=}P}$ and $\mathsf{Mod}_k\mathsf{P}$), so $\mathsf{SPP}$ is closed under polynomial-time Turing reductions; and $\mathsf{SPP}^{\mathsf{LWPP}}=\mathsf{LWPP}$, so $\mathsf{LWPP}$ is closed under polynomial-time Turing reductions too; whether $\mathsf{WPP}^{\mathsf{SPP}}=\mathsf{WPP}$ is open (Fenner, Fortnow and Kurtz only show $\mathsf{WPP}^{\mathsf{SPP}}\subseteq\mathsf{C_{=}P}\cap\mathsf{coC_{=}P}$). Finally $\mathsf{FewP}\subseteq\mathsf{SPP}$, so $\mathsf{FewP}$ is low for $\mathsf{SPP}$ and $\mathsf{GapP}$.

## Proof sketch

For $A\in\mathsf{SPP}$, replace each oracle query by a guessed answer weighted by the SPP gap of the query (which is $1$ for the true answer and $0$ for the wrong one), multiplying gaps along a path; adaptive queries multiply polynomially many such factors, which stays in $\mathsf{GapP}$. Conversely, $\chi_A\in\mathsf{GapP}^A=\mathsf{GapP}$ shows $A\in\mathsf{SPP}$; and if $\mathsf{SPP}^A=\mathsf{SPP}$ then $A\in\mathsf{P}^A\subseteq\mathsf{SPP}$.

## Depends on

- [GapP and the gap-definable classes SPP, WPP, LWPP, AWPP, C=P and Mod_kP](gap-definable-classes.md)
- [Polynomial time with an oracle](../../complexity-classes/time-and-space-complexity-classes/pwith-oracle.md)

## Proof depends on

- [Closure properties of GapP](gapp-closure.md)

## Sources

- Stephen A. Fenner, Lance J. Fortnow and Stuart A. Kurtz, "Gap-Definable Counting Classes", Journal of Computer and System Sciences 48(1), 1994, Theorem 5.5, Corollaries 5.6–5.12, the discussion after Definition 5.13 in Section 5 (where the proof of Theorem 5.5 is adapted to show $\mathsf{SPP}^{\mathsf{LWPP}}=\mathsf{LWPP}$, and lowness of $\mathsf{LWPP}$ for $\mathsf{WPP}$ or $\mathsf{LWPP}$ is left unproved), and the open questions at the end of the paper.
