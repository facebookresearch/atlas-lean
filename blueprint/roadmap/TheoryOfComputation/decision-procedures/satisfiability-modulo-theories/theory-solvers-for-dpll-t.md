# Theory solvers for DPLL(T)

Let $T$ be a first-order theory. A *theory solver* for $T$ takes a finite set $M$ of literals over the theory's atoms and either reports that $M$ is $T$-consistent or returns a $T$-inconsistent subset $E \subseteq M$ (a conflict explanation). It may also perform *theory propagation*: return a literal $l$ not in $M$ together with a subset $E \subseteq M$ such that $E \models_T l$. A solver is *sound* if every reported conflict is $T$-inconsistent and every propagated literal is $T$-entailed by its explanation, and *complete* if it reports a conflict whenever $M$ is $T$-inconsistent.

## Depends on

- [Satisfiability of a CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnfsat.md)

## Sources

- R. Nieuwenhuis, A. Oliveras and C. Tinelli, "Solving SAT and SAT modulo theories: from an abstract Davis–Putnam–Logemann–Loveland procedure to DPLL(T)", *Journal of the ACM* 53(6):937–977, 2006, <https://www.cs.upc.edu/~roberto/papers/JACM2006.pdf>
