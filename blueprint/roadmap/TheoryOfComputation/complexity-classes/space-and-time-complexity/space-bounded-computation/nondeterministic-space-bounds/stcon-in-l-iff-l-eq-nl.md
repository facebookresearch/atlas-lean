# Directed connectivity is in L iff L = NL

$\mathrm{STCON}\in\mathsf{L}$ if and only if $\mathsf{NL}=\mathsf{L}$; the same holds with STCON replaced by any $\mathsf{NL}$-complete problem under logarithmic-space many-one reductions (for instance strong connectivity of digraphs).

## Proof sketch

$\mathsf{L}$ is closed under logspace reductions because logspace functions compose; since STCON is NL-complete, a logspace algorithm for it yields one for every NL language. The converse is immediate as STCON ∈ NL.

## Depends on

- [Directed $s$-$t$ connectivity](../../../../completeness-other-classes/directed-s-t-connectivity/stcon-dec.md)
- [Deterministic logarithmic space](../../../time-and-space-complexity-classes/log-space.md)
- [The complexity class NL](../../../time-and-space-complexity-classes/nl.md)

## Proof depends on

- [ST-connectivity is NL-complete](../../../../completeness-other-classes/directed-s-t-connectivity/stcon-nl-complete.md)
- [Log-space many-one reductions](../../../time-and-space-complexity-classes/log-space-red.md)
- [Log-space computable functions](../../../time-and-space-complexity-classes/log-space-computable.md)
- [Logarithmic-space computable functions compose](../logspace-composition-and-layered-reachability/logspace-functions-compose.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
