# FO(LFP) definability is closed under first-order reductions on ordered structures

If $K \le_{\mathrm{fo}} K'$ on canonically ordered structures via a full-tuple interpretation and $K'$ is FO(LFP)-definable, then $K$ is FO(LFP)-definable. Combined with the Immerman–Vardi theorem, every ordered query that first-order reduces to a polynomial-time problem with an FO(LFP) definition, such as the monotone circuit value problem, is itself FO(LFP)-definable.

## Proof sketch

Pull back the defining FO(LFP) sentence along the interpretation; the pullback preserves positivity and nested fixed points.

## Depends on

- [Ordered first-order interpretations and first-order queries](../ordered-structures-and-arithmetic/ordered-first-order-interpretations.md)
- [Definability in FO + LFP](../immerman-vardi-theorem/og-lfpdefinable.md)

## Proof depends on

- [Full-tuple interpretations pull back FO(LFP), FO(TC) and SO∃-Horn sentences](../ordered-structures-and-arithmetic/full-tuple-interpretations-preserve-logics.md)
- [Immerman-Vardi: FO + least fixed point is P on ordered structures](../immerman-vardi-theorem/immerman-vardi.md)

## Sources

- N. Immerman, "Relational Queries Computable in Polynomial Time", Information and Control 68(1–3), 86–104, 1986.
- N. Immerman, Descriptive Complexity, Springer, 1999.
