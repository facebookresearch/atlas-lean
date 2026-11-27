# Full-tuple interpretations pull back FO(LFP), FO(TC) and SO∃-Horn sentences

Let $I$ be a full-tuple ordered interpretation of dimension $k$. For every sentence $\Phi$ of FO(LFP) (respectively FO(TC), FO(DTC)) over the target vocabulary with its canonical numeric predicates, there is a sentence $\Phi^I$ of the same logic over the source such that $\mathfrak{A} \models \Phi^I$ iff $I(\mathfrak{A}) \models \Phi$. A fixed point or closure over $r$-tuples of target elements becomes one over $rk$-tuples of source elements, and positivity (polarity of fixed-point variables and of closure operators) is preserved. Hence FO(LFP), FO(TC) and FO(DTC) definability on ordered structures are closed under first-order reductions by full-tuple interpretations. For SO∃-Horn the same substitution, with relation variables of arity $r$ becoming relation variables of arity $rk$, gives an SO∃-Horn sentence with first-order guards, which guard elimination turns into one with quantifier-free guards on structures with a built-in successor; so SO∃-Horn definability on such structures is closed under these reductions as well.

## Proof sketch

Replace each target variable by a block of $k$ coordinates, using the definable lexicographic numeric predicates on tuples; the pullback of fixed points uses the bijection between source $rk$-tuples and target $r$-tuples, which commutes with the stage operator.

## Depends on

- [Ordered first-order interpretations and first-order queries](ordered-first-order-interpretations.md)
- [Formulas of first-order logic with least fixed points](../immerman-vardi-theorem/ogfo.md)
- [Formulas of first-order logic with transitive closure](../transitive-closure-logic-and-nl/tcfo.md)

## Proof depends on

- [Lexicographic order, successor and BIT on tuples are definable](lexicographic-tuple-numeric-predicates.md)
- [Pullback of formulas along interpretations](../first-order-interpretations-and-reductions/pullback-along-interpretations.md)
- [Guard elimination for SO∃-Horn on successor structures](../second-order-horn-logic/so-horn-guard-elimination.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
- N. Immerman, "Relational Queries Computable in Polynomial Time", Information and Control 68(1–3), 86–104, 1986.
- N. Immerman, "Languages That Capture Complexity Classes", SIAM Journal on Computing 16(4), 760–778, 1987.
