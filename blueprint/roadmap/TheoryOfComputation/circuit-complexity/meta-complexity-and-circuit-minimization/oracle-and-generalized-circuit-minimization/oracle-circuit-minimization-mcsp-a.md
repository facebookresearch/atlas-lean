# Oracle circuit minimization MCSP^A and MKTP^A

For a fixed oracle $A$, $\mathrm{MCSP}^A$ asks whether a truth table has a circuit of size at most $s$ that may also use $A$-oracle gates, and $\mathrm{MKTP}^A$ asks the same question for KT complexity relative to $A$. When $A$ is complete for a class $\mathcal{C}$ one writes $\mathrm{MCSP}^{\mathcal{C}}$.

**Definition (Allender–Holden–Kabanets).** Let $A$ be a language.

- $\mathrm{MCSP}^A=\{(f,s) : f \text{ has } A\text{-oracle circuits of size } s\}$, where $f$ is a string of length $2^m$ giving the truth table of an $m$-variate Boolean function and circuits may contain oracle gates that query $A$.
- $\mathrm{KT}^A(x)=\min\{|d|+t : \forall b\in\{0,1,*\}\ \forall i\le|x|+1,\ U^{A}(d,i,b) \text{ accepts within } t \text{ steps iff } x_i=b\}$, where $U$ is the fixed efficient universal machine of the [KT page](../reductions-to-mcsp-and-mktp/kt-complexity-and-mktp.md) (logarithmic time and linear space simulation overhead), given random access to $A$ and to $d$, and $x_{|x|+1}=*$.
- $\mathrm{MKTP}^A=\{(x,i) : \mathrm{KT}^A(x)\le i\}$.

Allender, Holden and Kabanets state their hardness results for each of three conventions for the size of an oracle circuit: the number of gates (including oracle gates), the number of wires, or the number of bits of a standard encoding; the resulting versions of $\mathrm{MCSP}^A$ are not known to reduce to one another efficiently. The quantitative comparison with KT is separate and needs its own convention: $\mathrm{SIZE}^A$ and $\mathrm{KT}^A$ are polynomially related when the size of an oracle circuit is its number of input gates plus its number of connections, so that every oracle query is charged its length. For the PSPACE-complete oracle QBF, $\mathrm{MCSP}^{\mathrm{QBF}}$ is complete for PSPACE under ZPP reductions.

## Expansion

The source warns that intuition is a poor guide when comparing $\mathrm{MCSP}^A$ with $\mathrm{MCSP}^B$ for given oracles $A$ and $B$. The PSPACE-completeness of $\mathrm{MCSP}^{\mathrm{QBF}}$ under ZPP reductions comes from $\mathrm{PSPACE}=\mathrm{ZPP}^{R_{\mathrm{KS}}}$, since KS complexity is, up to a constant factor, KT complexity relative to a set complete for $\mathrm{DSPACE}(n)$ under linear-time reductions.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [KT complexity and the minimum KT problem MKTP](../reductions-to-mcsp-and-mktp/kt-complexity-and-mktp.md)
- [Oracle circuits and local circuit classes](../../hardness-magnification/oracle-circuits-and-local-circuit-classes.md)
- [PSPACE](../../../complexity-classes/time-and-space-complexity-classes/pspace.md)
- [ZPP](../../../complexity-classes/time-and-space-complexity-classes/zpp.md)
- [TQBF is PSPACE-complete](../../../completeness-other-classes/true-quantified-boolean-formulas/tqbf-pspace-complete.md)

## Proof depends on

- [Sets of random strings are hard for EXP and PSPACE](../reductions-to-mcsp-and-mktp/random-string-oracles-are-hard-for-exp-and-pspace.md)

## Sources

- Eric Allender, Dhiraj Holden, Valentine Kabanets, "The Minimum Oracle Circuit Size Problem", *Symposium on Theoretical Aspects of Computer Science (STACS)*, 2015, https://doi.org/10.4230/LIPIcs.STACS.2015.21 (Definitions 1 to 3, abstract and Section 2).
- Eric Allender, Harry Buhrman, Michal Koucký, Dieter van Melkebeek, Detlef Ronneburger, "Power from Random Strings", *SIAM Journal on Computing* 35(6), 2006, https://doi.org/10.1137/050628994 (Theorems 4 and 12, numbering of the ECCC TR02-028 revision 1 edition; Proposition 5 and Theorem 11 of the journal version).
- Eric Allender, Dieter van Melkebeek, "A Comment Regarding KT and Circuit Size", note, https://people.cs.rutgers.edu/~allender/papers/clarification.pdf (the circuit-size convention for the journal Theorem 11).
