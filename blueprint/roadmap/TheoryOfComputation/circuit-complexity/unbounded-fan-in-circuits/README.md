# Unbounded fan-in circuits

## The `ACGate` basis as a CSLib signature

- [Operation symbols of the unbounded fan-in basis](acop.md)
- [Unbounded fan-in signature](ac-signature.md)
- [Boolean meaning of the unbounded fan-in basis](ac-interpretation.md)

## Translation

- [Appending a flat gate to a straight-line circuit](snoc-acgate.md)
- [Straight-line circuit of the first gates of a flat circuit](to-circuit-up-to.md)
- [Straight-line circuit of a flat circuit](to-circuit.md)

## Flat evaluation and depth, one gate at a time

- [Flat evaluation has one value per gate](length-circuit-eval.md)
- [Flat depths have one entry per gate](length-circuit-depths.md)
- [Evaluating one more flat gate](circuit-eval-append-singleton.md)
- [Measuring one more flat gate](circuit-depths-append-singleton.md)

## Evaluation

- [Constant gates in the unbounded fan-in basis](ac-interpretation-const.md)
- [Negation in the unbounded fan-in basis](ac-interpretation-not.md)
- [AND gates in the unbounded fan-in basis](ac-interpretation-and.md)
- [OR gates in the unbounded fan-in basis](ac-interpretation-or.md)
- [MOD gates in the unbounded fan-in basis](ac-interpretation-mod.md)
- [Appending a flat gate keeps the earlier output values](eval-snoc-acgate-cast-succ.md)
- [Value of an appended flat gate](eval-snoc-acgate-last.md)
- [The straight-line circuit computes every flat gate](eval-to-circuit.md)
- [Evaluating the straight-line circuit gives the flat evaluation](of-fn-eval-to-circuit.md)

## Size

- [Appending a flat gate adds at most one gate](size-snoc-acgate-le.md)
- [The straight-line circuit is no larger than the flat circuit](size-to-circuit-le.md)
- [Exact size of the straight-line circuit](size-to-circuit.md)

## Depth

- [Appending a flat gate keeps the earlier output depths](output-depths-snoc-acgate-cast-succ.md)
- [Depth of an appended constant gate](output-depths-snoc-acgate-const.md)
- [Depth of an appended nonconstant flat gate](output-depths-snoc-acgate-last.md)
- [Outputs are at least as deep as their flat gates](get-elem-circuit-depths-le-output-depths.md)
- [Outputs are at most one level deeper than their flat gates](output-depths-to-circuit-le.md)
- [Output depths without constant gates](output-depths-to-circuit-eq.md)
- [The straight-line circuit is at least as deep as the flat circuit](circuit-depth-le-depth-to-circuit.md)
- [The straight-line circuit is at most one level deeper than the flat circuit](depth-to-circuit-le.md)
- [Depth of the straight-line circuit without constant gates](depth-to-circuit-eq.md)

## Exact depth, constants included

- [Gate depth with constants at depth one](ac-gate-depth-of.md)
- [Gate depths with constants at depth one](ac-circuit-depths.md)
- [One depth per gate with constants at depth one](length-ac-circuit-depths.md)
- [Measuring one more gate with constants at depth one](ac-circuit-depths-append-singleton.md)
- [Exact output depths of the straight-line circuit](output-depths-to-circuit.md)
- [Output depths of the straight-line circuit as a list](of-fn-output-depths-to-circuit.md)
- [Exact depth of the straight-line circuit](depth-to-circuit.md)
