# Trakhtenbrot's theorem: finite satisfiability is undecidable

The set of first-order sentences (over relational vocabularies) that are finitely satisfiable is recursively enumerable but not decidable. Consequently the set of finitely valid sentences is not recursively enumerable, so there is no sound and complete proof system for validity over finite structures, and there are finitely valid sentences that are not provable in any given recursively axiomatized sound system.

## Proof sketch

Reduce the halting problem: for a partial recursive code $c$ and input $n$, build a sentence describing, inside a finite arithmetic initial segment, the graph of the step-bounded evaluator of $c$ together with axioms forcing a halting computation on $n$. It is finitely satisfiable iff the computation halts (take the segment large enough to contain the run). Decidability of finite satisfiability would decide halting.

## Depends on

- [Finite satisfiability and finite validity](finite-satisfiability-and-validity.md)
- [Multi-stack decidable predicates are exactly the computable predicates](../../computability/decidable-and-recognizable-predicates/tm2-decidable-iff-computable-pred.md)

## Proof depends on

- [Finite satisfiability is recursively enumerable](finite-satisfiability-recursively-enumerable.md)
- [Axiomatizing arithmetic on finite initial segments](arithmetic-on-finite-initial-segments.md)
- [Halting is undecidable](../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Sources

- B. A. Trakhtenbrot, "Impossibility of an Algorithm for the Decision Problem in Finite Classes", Doklady Akademii Nauk SSSR 70, 569–572, 1950.
- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
