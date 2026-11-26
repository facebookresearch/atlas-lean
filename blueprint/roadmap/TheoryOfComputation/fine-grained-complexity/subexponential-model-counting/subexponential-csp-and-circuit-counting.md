# Subexponential counting for bounded-arity Boolean #CSP and #Circuit-SAT

For every fixed arity $r$, the number of satisfying assignments of a Boolean constraint satisfaction instance with $n$ variables and constraints of arity at most $r$ (given by truth tables) is computable in time $2^{o(n)}\mathrm{poly}(L)$. Consequently, for Boolean circuits over any fixed bounded fan-in basis, the number of satisfying inputs (and satisfiability) is computable in time $2^{o(n+g)}$ for $n$ inputs and $g$ gates, via a polynomial-time compilation to CSP in which the count is multiplied by an explicit power of two.

## Proof sketch

Encode each constraint as a constant number of $r$-clauses on the same variables, preserving the model count exactly, then apply the subexponential bounded-width counter; a circuit becomes a CSP with one variable per wire and one constraint per gate.

## Depends on

- [The exponents s_k of k-SAT and #k-SAT](../sat-exponents-and-hypotheses/k-sat-exponents.md)

## Proof depends on

- [Subexponential exact model counting for bounded-width CNF](subexponential-model-counting.md)

## Sources

- OpenAI, "The Exponential Time Hypothesis is False", Manuscript, 2026.
