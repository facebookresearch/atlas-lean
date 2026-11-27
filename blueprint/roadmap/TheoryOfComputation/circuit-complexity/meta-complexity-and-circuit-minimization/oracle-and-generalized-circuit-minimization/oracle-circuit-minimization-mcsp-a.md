# Oracle circuit minimization MCSP^A and MKTP^A

For a fixed oracle $A$, $\mathrm{MCSP}^A$ asks whether a truth table has a circuit of size at most $s$ that may also use $A$-oracle gates, and $\mathrm{MKTP}^A$ asks the same question for KT complexity relative to $A$. When $A$ is complete for a class $\mathcal{C}$ one writes $\mathrm{MCSP}^{\mathcal{C}}$.

**Definition (Allender–Holden–Kabanets).** Let $A$ be a language.

- $\mathrm{MCSP}^A=\{(f,s) : f \text{ has } A\text{-oracle circuits of size } s\}$, where $f$ is a string of length $2^m$ giving the truth table of an $m$-variate Boolean function and circuits may contain oracle gates that query $A$.
- $\mathrm{KT}^A(x)=\min\{|d|+t : \forall b\in\{0,1,*\}\ \forall i\le|x|+1,\ U^{A}(d,i,b) \text{ accepts within } t \text{ steps iff } x_i=b\}$, where $U$ is a fixed universal machine with random access to $A$ and to $d$, and $x_{|x|+1}=*$.
- $\mathrm{MKTP}^A=\{(x,i) : \mathrm{KT}^A(x)\le i\}$.

The results stated for these problems hold whether circuit size counts gates (including oracle gates), wires, or bits of a standard encoding; the resulting versions are not known to reduce to one another efficiently. $\mathrm{SIZE}^A$ and $\mathrm{KT}^A$ are polynomially related: $\mathrm{SIZE}^A(x)=O(\mathrm{KT}^A(x)^3)$ and $\mathrm{KT}^A(x)=O(\mathrm{SIZE}^A(x)^2+\log|x|)$. For the PSPACE-complete oracle QBF, $\mathrm{MCSP}^{\mathrm{QBF}}$ is complete for PSPACE under ZPP reductions.

## Expansion

The source warns that intuition is a poor guide when comparing $\mathrm{MCSP}^A$ with $\mathrm{MCSP}^B$ for given oracles $A$ and $B$. The PSPACE-completeness of $\mathrm{MCSP}^{\mathrm{QBF}}$ under ZPP reductions comes from $\mathrm{PSPACE}=\mathrm{ZPP}^{R_{\mathrm{KS}}}$, since KS complexity is KT complexity relative to a linear-space-complete set.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [KT complexity and the minimum KT problem MKTP](../reductions-to-mcsp-and-mktp/kt-complexity-and-mktp.md)

## Proof depends on

- [Sets of random strings are hard for EXP and PSPACE](../reductions-to-mcsp-and-mktp/random-string-oracles-are-hard-for-exp-and-pspace.md)

## Sources

- Eric Allender, Dhiraj Holden, Valentine Kabanets, "The Minimum Oracle Circuit Size Problem", *Symposium on Theoretical Aspects of Computer Science (STACS)*, 2015, https://doi.org/10.4230/LIPIcs.STACS.2015.21 (Definitions 1 to 3, abstract and Section 2).
- Eric Allender, Harry Buhrman, Michal Koucký, Dieter van Melkebeek, Detlef Ronneburger, "Power from Random Strings", *SIAM Journal on Computing* 35(6), 2006, https://doi.org/10.1137/050628994 (Theorems 4, 5 and 12, numbering of the ECCC TR02-028 revision 1 edition).
