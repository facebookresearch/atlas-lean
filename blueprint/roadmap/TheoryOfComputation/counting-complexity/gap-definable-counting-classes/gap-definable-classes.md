# GapP and the gap-definable classes SPP, WPP, LWPP, AWPP, C=P and Mod_kP

$\mathsf{GapP}=\{f-g : f,g\in\#\mathsf{P}\}$, equivalently the differences of accepting and rejecting path counts of polynomial-time nondeterministic machines. In terms of $f\in\mathsf{GapP}$:

- $\mathsf{C_{=}P}=\{\{x: f(x)=0\}\}$; $\mathsf{Mod}_k\mathsf{P}=\{\{x : f(x)\not\equiv0\pmod k\}\}$ ($\oplus\mathsf{P}$ for $k=2$);
- $\mathsf{SPP}$: $f(x)\in\{0,1\}$ with $f(x)=1$ iff $x\in L$;
- $\mathsf{WPP}$: $f(x)\in\{0,g(x)\}$ for some polynomial-time computable $g>0$; $\mathsf{LWPP}$ when $g$ depends only on $|x|$;
- $\mathsf{AWPP}$: for every polynomial $q$ there is $f$ and a polynomial $r$ with $f(x)/2^{r(|x|)}\in[1-2^{-q},1]$ on members and $\in[0,2^{-q}]$ on non-members.

One has $\mathsf{UP}\subseteq\mathsf{FewP}\subseteq\mathsf{SPP}\subseteq\mathsf{LWPP}\subseteq\mathsf{WPP}\subseteq\mathsf{C_{=}P}$, $\mathsf{SPP}\subseteq\mathsf{Mod}_k\mathsf{P}$, and $\mathsf{BQP}\subseteq\mathsf{AWPP}\subseteq\mathsf{PP}$.

## Depends on

- [The counting class $\#P$](../../complexity-classes/time-and-space-complexity-classes/sharp-p.md)
- [Probabilistic polynomial time with unbounded error](../../complexity-classes/time-and-space-complexity-classes/pp.md)
- [Unambiguous and few-witness polynomial time: UP and FewP](../../complexity-classes/structural-complexity/reducibilities-and-isomorphism/up-and-fewp.md)

## Sources

- Stephen A. Fenner, Lance J. Fortnow and Stuart A. Kurtz, "Gap-Definable Counting Classes", Journal of Computer and System Sciences 48(1), 1994, Proposition 3.5, Definition 4.1, Proposition 4.2, Sections 5 (SPP, Definition 5.13 of WPP and LWPP) and Corollaries 5.10–5.11.
- Stephen A. Fenner, "PP-Lowness and a Simple Definition of AWPP", Theory of Computing Systems 36(2), 2003.
- Richard Beigel and John Gill, "Counting Classes: Thresholds, Parity, Mods, and Fewness", Theoretical Computer Science 103(1), 1992.
