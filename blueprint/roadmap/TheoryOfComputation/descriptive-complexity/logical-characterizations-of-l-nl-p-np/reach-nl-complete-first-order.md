# Immerman: REACH is NL-complete under first-order reductions

Let $\mathrm{REACH}$ be the query on ordered directed graphs 'is $\max$ reachable from $0$?'. Then $\mathrm{REACH}\in\mathsf{NL}$, and every query on ordered structures whose encoded language is in $\mathsf{NL}$ first-order reduces to $\mathrm{REACH}$ (by a positive-dimensional full-tuple interpretation). Hence REACH is $\mathsf{NL}$-complete under first-order (and logspace) reductions.

## Proof sketch

For an NL machine, the configurations of logarithmic size are $k$-tuples of universe elements for a constant $k$; the step relation between configurations is first-order definable from the input relations using BIT to read the input-head position. Accepting runs are paths from the initial to the accepting configuration.

## Depends on

- [First-order and quantifier-free reductions](../first-order-interpretations-and-reductions/first-order-reductions.md)
- [The complexity class NL](../../complexity-classes/time-and-space-complexity-classes/nl.md)
- [First-order reductions between queries on ordered structures](../first-order-projections/first-order-reductions-on-ordered-structures.md)

## Proof depends on

- [ST-connectivity is NL-complete](../../completeness-other-classes/directed-s-t-connectivity/stcon-nl-complete.md)
- [First-order reductions are computable in logarithmic space](../first-order-interpretations-and-reductions/first-order-reductions-logspace-computable.md)

## Sources

- Neil Immerman, "Descriptive Complexity", Springer, 1999, Theorem 3.16 and Exercise 3.20.
