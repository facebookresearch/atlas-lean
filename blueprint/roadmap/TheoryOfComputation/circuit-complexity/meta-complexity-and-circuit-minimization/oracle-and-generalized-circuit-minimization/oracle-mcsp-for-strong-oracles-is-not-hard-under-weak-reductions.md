# Oracle MCSP for strong oracles is not hard under weak reductions

$\mathrm{MCSP}^{\mathrm{QBF}}$, although PSPACE-complete under ZPP reductions, is not PSPACE-hard under logspace reductions, and for any oracle $A$ hard for the polynomial hierarchy, $\mathrm{MCSP}^A$ is not even $\mathrm{TC}^0$-hard under uniform $\mathrm{AC}^0$ reductions.

**Theorem (Allender–Holden–Kabanets).** Each statement also holds with MKTP in place of MCSP. Uniform $\mathrm{AC}^0$ reductions are as in the source, whose arguments use Dlogtime uniformity (proofs of Proposition 10 and Lemma 21); this is not the log-space uniformity of the linked uniform-family page, which supplies only the notion of a uniform circuit family.

1. If $\mathrm{MCSP}^{\mathrm{EXP}}$ is hard for NP under polynomial-time reductions, then $\mathrm{NEXP}=\mathrm{EXP}$.
2. If $\mathrm{MCSP}^{\mathrm{QBF}}$ is hard for NP under logspace reductions, then $\mathrm{NEXP}=\mathrm{PSPACE}$; if it is hard for P under logspace reductions, then $\mathrm{EXP}=\mathrm{PSPACE}$.
3. Neither $\mathrm{MCSP}^{\mathrm{QBF}}$ nor $\mathrm{MKTP}^{\mathrm{QBF}}$ is hard for PSPACE under logspace reductions.
4. For every language $A$ that is hard for PH under P/poly reductions, $\mathrm{MCSP}^A$ is not hard for $\mathrm{TC}^0$ under uniform $\mathrm{AC}^0$ reductions. In particular $\mathrm{MCSP}^{\oplus\mathrm{P}}$ is not $\mathrm{TC}^0$-hard under uniform $\mathrm{AC}^0$ reductions, and if $\mathrm{MCSP}^A$ is $\mathrm{TC}^0$-hard under uniform $\mathrm{AC}^0$ reductions for some $A$, then $\mathrm{NP}^A\not\subseteq\mathrm{SIZE}^A[\mathrm{poly}]$.

## Expansion

The proofs pass to succinct versions. The B-succinct version of $\mathrm{MCSP}^A$, whose instances are given by B-oracle circuits for the truth table, lies in $(\Sigma^p_2)^A$ when $B\le^p_T A$. A reduction from SAT whose output bits are computable within the oracle's class becomes a reduction from succinct SAT, which is NEXP-complete, to succinct $\mathrm{MCSP}^A$: for item 1 this puts NEXP in $(\Sigma^p_2)^{\mathrm{EXP}}=\mathrm{EXP}$, and for item 2 in PSPACE. Repeating the argument with PSPACE in place of NP would give $\mathrm{EXPSPACE}=\mathrm{PSPACE}$, contradicting the space hierarchy theorem, which is item 3. For item 4, a uniform $\mathrm{AC}^0$ reduction yields a language in PH that requires $A$-oracle circuits of size $2^{\Omega(n)}$ almost everywhere, which contradicts PH-hardness of $A$ under P/poly reductions; the step uses Håstad's bound that depth-three circuits for PARITY on $m$ bits need size $2^{\Omega(\sqrt{m})}$.


Known unstated proof prerequisites needed before this node is ready for formalization:

- EXPSPACE-completeness of succinct QBF (Allender–Holden–Kabanets Section 1.3 and Corollary 19)
- Agrawal's theorem that sets hard under uniform $\mathrm{AC}^0$ reductions for a class closed under $\mathrm{TC}^0$ reductions are hard under length-increasing (uniform $\mathrm{AC}^0$)-uniform $\mathrm{NC}^0$ reductions (M. Agrawal, *J. Comput. Syst. Sci.* 77(1), 2011, Theorems 5.1 and 6.2, extended to hard sets in Allender–Holden–Kabanets Lemma 21)
- Non-uniform inclusion $\mathrm{PH} \subseteq \mathrm{SIZE}^{\oplus\mathrm{P}}[\mathrm{poly}]$ (fixing the random bits of Toda's first step, used in Corollary 23)

## Depends on

- [Oracle circuit minimization MCSP^A and MKTP^A](oracle-circuit-minimization-mcsp-a.md)
- [TQBF is PSPACE-complete](../../../completeness-other-classes/true-quantified-boolean-formulas/tqbf-pspace-complete.md)
- [Log-space reductions](../../../complexity-classes/time-and-space-complexity-classes/log-space-red.md)
- [The polynomial hierarchy](../../../complexity-classes/time-and-space-complexity-classes/ph.md)
- [The complexity class NEXP](../../../complexity-classes/time-and-space-complexity-classes/nexp.md)
- [PSPACE](../../../complexity-classes/time-and-space-complexity-classes/pspace.md)
- [The class EXP](../../../complexity-classes/time-and-space-complexity-classes/exp.md)
- [Uniform circuit families](../../../complexity-classes/time-and-space-complexity-classes/uniform-circuit-family.md)
- [AC0](../../../complexity-classes/time-and-space-complexity-classes/ac0.md)

## Proof depends on

- [Space hierarchy theorem](../../../hierarchy-theorems-and-barriers/space-hierarchy-theorem/space-hierarchy.md)
- [Depth-d circuit size of parity](../../lower-bounds-for-ac0-circuits/depth-d-circuit-size-of-parity.md)
- [Succinct 3SAT is NEXP-complete](../../../completeness-other-classes/succinct-3sat/succinct-three-sat-nexp-complete.md)
- [Succinct Circuit Value is EXP-complete](../../../completeness-other-classes/succinct-circuit-value-problem/succinct-circuit-value-exp-complete.md)
- [Randomized reduction from the polynomial hierarchy to parity satisfiability](../../../counting-complexity/randomized-reduction-from-ph-to-parity-sat.md)

## Sources

- Eric Allender, Dhiraj Holden, Valentine Kabanets, "The Minimum Oracle Circuit Size Problem", *Symposium on Theoretical Aspects of Computer Science (STACS)*, 2015, https://doi.org/10.4230/LIPIcs.STACS.2015.21 (Theorems 7, 9, 15, 17 and 20, Proposition 10, Corollaries 8, 18, 19, 23 and 24, Lemma 21).
