# Sets of random strings are hard for EXP and PSPACE

Sets of resource-bounded random strings are powerful oracles: $\mathrm{EXP}=\mathrm{NP}^{R_{\mathrm{Kt}}}$, $\mathrm{PSPACE}=\mathrm{ZPP}^{R_{\mathrm{KS}}}\subseteq\mathrm{P}^{R_K}$, and $R_{\mathrm{Kt}}$ and $R_{\mathrm{KS}}$ are complete for EXP and PSPACE under P/poly truth-table reductions.

Let $\mathrm{KS}(x)=\min\{|d|+s : U(d)=x \text{ in space at most } s\}$, where $U$, here and in $\mathrm{KT}^A$, is the fixed efficient universal machine of the [KT page](kt-complexity-and-mktp.md), which simulates with logarithmic time and linear space overhead. For a measure $\mu\in\{K,\mathrm{Kt},\mathrm{KS},\mathrm{KT}\}$ let $R_\mu=\{x : \mu(x)\ge|x|/2\}$ (any threshold $|x|^{\varepsilon}$, $0<\varepsilon<1$, works). A language $A$ is *PSPACE-robust* if $\mathrm{PSPACE}^A=\mathrm{P}^A$.

**Theorem (Allender–Buhrman–Koucký–van Melkebeek–Ronneburger).**

1. If $A$ is PSPACE-robust and $L$ has polynomial density with $\mathrm{KT}^A(x)>|x|^{\gamma}$ for all $x\in L$ and some constant $0<\gamma<1$, then $A\le^{\mathrm{P/poly}}_{tt}L$.
2. $R_{\mathrm{Kt}}$ is complete for EXP and $R_{\mathrm{KS}}$ is complete for PSPACE under $\le^{\mathrm{P/poly}}_{tt}$ reductions.
3. Every recursively enumerable set is $\le^{\mathrm{P/poly}}_{tt}$-reducible to $R_K$.
4. $\mathrm{EXP}=\mathrm{NP}^{R_{\mathrm{Kt}}}$, $\mathrm{PSPACE}=\mathrm{ZPP}^{R_{\mathrm{KS}}}$, and $\mathrm{PSPACE}\subseteq\mathrm{P}^{R_K}$.

The hardness statements hold for every dense set containing no strings of low complexity in the respective measure. In contrast, $R_{\mathrm{KS}}$ is not hard for PSPACE under logspace Turing reductions, so the reductions above cannot be made that weak.

## Expansion

The proofs use relativizing hardness-versus-randomness constructions in the contrapositive. A generator built from a complete function $f$ (Babai–Fortnow–Nisan–Wigderson and Klivans–van Melkebeek, or Impagliazzo–Wigderson) has outputs of low $\mathrm{KT}^A$ complexity, so a dense set of random strings distinguishes it from uniform; the reconstruction procedure then yields small oracle circuits for $f$. For the uniform results the complete problems used are downward and random self-reducible, which lets the circuits be found and checked. These arguments do not relativize.

## Depends on

- [KT complexity and the minimum KT problem MKTP](kt-complexity-and-mktp.md)
- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)
- [Kolmogorov complexity](../../../kolmogorov-complexity/k.md)
- [The class EXP](../../../complexity-classes/time-and-space-complexity-classes/exp.md)
- [PSPACE](../../../complexity-classes/time-and-space-complexity-classes/pspace.md)
- [ZPP](../../../complexity-classes/time-and-space-complexity-classes/zpp.md)
- [Polynomial time with polynomial advice](../../../complexity-classes/time-and-space-complexity-classes/ppoly.md)
- [The complexity class P](../../../complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Distinguishers for the Nisan–Wigderson generator give short time-bounded descriptions](../../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/nisan-wigderson-reconstruction-gives-short-descriptions.md)
- [TQBF is PSPACE-complete](../../../completeness-other-classes/true-quantified-boolean-formulas/tqbf-pspace-complete.md)

## Sources

- Eric Allender, Harry Buhrman, Michal Koucký, Dieter van Melkebeek, Detlef Ronneburger, "Power from Random Strings", *SIAM Journal on Computing* 35(6), 2006, https://doi.org/10.1137/050628994 (Definitions 3 and 6, Theorems 7, 8 and 10 to 13, Corollary 9, numbering of the ECCC TR02-028 revision 1 edition; Proposition 5 of the journal version for the universal machine).
