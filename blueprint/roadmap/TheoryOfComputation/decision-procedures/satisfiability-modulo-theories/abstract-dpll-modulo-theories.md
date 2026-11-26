# Abstract DPLL modulo theories

This node covers the abstract DPLL(T) transition system of Nieuwenhuis, Oliveras and Tinelli: the abstract DPLL rules (unit propagation, decision, fail, backjump, learn, forget, restart) on states $M \parallel F$ of a partial assignment and a clause set, extended with theory propagation, theory learning and theory-based backjumping through a theory solver. Soundness of the theory steps holds for any sound theory solver. Termination holds only under side conditions on the strategy, which the source states for its own system: no infinite subderivations consisting only of theory learn and forget steps, and restarts whose periodicity increases unless a clause that is never forgotten has been learned. The characterization of final states applies to a state that is final for the basic rules and whose assignment is consistent in the theory: such a state is the fail state exactly when the clause set is unsatisfiable in the theory, and otherwise its assignment is a model in the theory. Reaching such a state therefore needs a theory solver that decides consistency of conjunctions of literals; soundness of its propagations and conflicts alone does not certify a satisfiable final state.

A good expansion fixes one version of the rule system and its side conditions against the cited paper, then states soundness, termination under those side conditions, and the characterization of final states as separate pages depending on the theory-solver interface.

## Expansion

This page becomes ready once these prerequisites are stated:

- CDCL correctness for a discipline (proof prerequisite)

## Sources

- R. Nieuwenhuis, A. Oliveras and C. Tinelli, "Solving SAT and SAT modulo theories: from an abstract Davis–Putnam–Logemann–Loveland procedure to DPLL(T)", *Journal of the ACM* 53(6):937–977, 2006, <https://www.cs.upc.edu/~roberto/papers/JACM2006.pdf>, Sections 2 and 3, Theorems 2.11, 3.7 and 3.10
