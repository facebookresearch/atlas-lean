# EVEN is not definable in fixed-point logic on unordered structures

There is no FO(LFP) sentence (and no FO(TC) sentence) over the empty vocabulary, or over the language of graphs, that holds exactly in the finite structures with an even number of elements. Consequently, on unordered finite structures FO(LFP) does not capture polynomial time, in contrast with the Immerman–Vardi theorem on ordered structures.

## Proof sketch

Fixed-point sentences are equivalent to $L^k_{\infty\omega}$ sentences, which obey the Kolaitis–Vardi 0-1 law, whereas the probability of EVEN alternates between $0$ and $1$. Over the empty vocabulary, structures of size at least $k$ are $k$-pebble equivalent.

## Depends on

- [Finite-variable logics $\mathrm{FO}^k$ and $L^k_{\infty\omega}$](../finite-variable-logics/finite-variable-logics.md)
- [Formulas of first-order logic with least fixed points](../immerman-vardi-theorem/ogfo.md)
- [Even cardinality is not first-order definable](../finite-model-theory/even-cardinality-is-not-first-order-definable.md)

## Proof depends on

- [Fixed-point logics embed into finite-variable infinitary logic](../finite-variable-logics/fixed-point-logic-in-finite-variable-infinitary-logic.md)
- [Kolaitis–Vardi: the 0-1 law for finite-variable infinitary logic $L^k_{\infty\omega}$](kolaitis-vardi-zero-one-law.md)

## Sources

- Ph. G. Kolaitis and M. Y. Vardi, "Infinitary Logics and 0-1 Laws", Information and Computation 98(2), 258–294, 1992.
- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
