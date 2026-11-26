# DPLL modulo theories transition system

Let $T$ be a first-order theory and $F$ a finite set of clauses of ground literals, with states $M \parallel F$ and FailState as in [abstract DPLL with learning](../../../Logic/propositional-logic/sat-solving/abstract-dpll-with-learning.md), where $M \models \neg C$ and undefinedness are read propositionally. Besides Decide, Fail, UnitPropagate and Restart, unchanged, the system has:

- **T-Learn:** $M \parallel F \Longrightarrow M \parallel F, C$ if each atom of $C$ occurs in $F$ or in $M$ and $F \models_T C$;
- **T-Forget:** $M \parallel F, C \Longrightarrow M \parallel F$ if $F \models_T C$;
- **T-Backjump:** $M\, l^d\, N \parallel F, C \Longrightarrow M\, l' \parallel F, C$ if $M\, l^d\, N \models \neg C$ and there is a clause $C' \vee l'$ with $F, C \models_T C' \vee l'$, $M \models \neg C'$, $l'$ undefined in $M$, and $l'$ or $\neg l'$ occurring in $F$ or in $M\, l^d\, N$;
- **TheoryPropagate:** $M \parallel F \Longrightarrow M\, l \parallel F$ if $M \models_T l$, $l$ or $\neg l$ occurs in $F$, and $l$ is undefined in $M$.

The *Basic DPLL modulo theories* system consists of Decide, Fail, UnitPropagate, TheoryPropagate and T-Backjump; the *Full* system $\mathcal{FT}$ adds T-Learn, T-Forget and Restart.

## Depends on

- [Abstract DPLL with learning](../../../Logic/propositional-logic/sat-solving/abstract-dpll-with-learning.md)

## Sources

- R. Nieuwenhuis, A. Oliveras and C. Tinelli, "Solving SAT and SAT modulo theories: from an abstract Davis–Putnam–Logemann–Loveland procedure to DPLL(T)", *Journal of the ACM* 53(6):937–977, 2006, <https://www.cs.upc.edu/~roberto/papers/JACM2006.pdf>, Section 3.3: Definition 3.2 (T-Learn, T-Forget, T-Backjump), Definition 3.3 (TheoryPropagate); Section 3.4: Definitions 3.4 and 3.5.
