# First-order reductions are computable in logarithmic space

Let $I$ be a first-order interpretation (possibly over ordered structures with $\mathrm{BIT}$). The map sending the binary encoding of a finite structure $\mathfrak{A}$ to the encoding of $I(\mathfrak{A})$ is computable in deterministic logarithmic space (and in $\mathrm{DLOGTIME}$-uniform $\mathrm{AC}^0$ when the domain formula is trivial, i.e. the image universe is all of $A^d$). Consequently $K \le_{\mathrm{fo}} K'$ implies that $K$ is logspace many-one reducible to $K'$, and completeness under first-order reductions implies completeness under logspace reductions.

## Proof sketch

Enumerate the candidate tuples of the output universe and the relation tuples with $O(\log n)$-bit counters, evaluating each fixed first-order formula by nested loops over the quantified variables; each loop needs one counter, and the formula is fixed.

## Depends on

- [First-order and quantifier-free reductions](first-order-reductions.md)
- [Binary encoding of finite relational structures](../finite-structures-and-definability/binary-encoding-of-finite-structures.md)
- [Log-space many-one reductions](../../complexity-classes/time-and-space-complexity-classes/log-space-red.md)

## Proof depends on

- [Pullback of formulas along interpretations](pullback-along-interpretations.md)
- [First-order model checking for a fixed sentence is in L](../logical-characterizations-of-l-nl-p-np/first-order-queries-in-logspace.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
