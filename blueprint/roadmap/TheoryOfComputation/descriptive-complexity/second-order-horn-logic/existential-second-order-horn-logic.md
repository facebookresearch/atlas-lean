# Existential second-order Horn logic

An *SO∃-Horn* sentence has the form $\exists R_1 \cdots R_m\, \bigwedge_i \forall \bar x_i\, C_i$ where each clause $C_i$ is $\gamma \wedge R_{j_1}(\bar y_1) \wedge \dots \wedge R_{j_l}(\bar y_l) \to H$ with a *guard* $\gamma$ that is a first-order formula of the base vocabulary, body atoms applying relation variables to clause variables, and head $H$ either one relation-variable atom (a definite clause) or $\bot$ (a goal clause). The Horn restriction applies only to the quantified relation variables; base-vocabulary symbols may occur arbitrarily in guards. In Grädel's SO∃-Horn the guards are quantifier-free, so the first-order part is universal; the variant with first-order guards is reduced to it on structures with a successor relation by guard elimination.

## Depends on

- [Relational second-order logic on finite structures](../second-order-logic-on-finite-structures/relational-second-order-logic.md)
- [Horn formula](../../../Logic/propositional-logic/horn-satisfiability/is-horn.md)

## Sources

- E. Grädel, "Capturing Complexity Classes by Fragments of Second-Order Logic", Theoretical Computer Science 101(1), 35–57, 1992.
- N. Immerman, Descriptive Complexity, Springer, 1999.
