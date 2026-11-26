# Korten: solving Avoid yields hard truth tables

Let $\mathrm{TT}_s : \{0,1\}^{O(s \log s)} \to \{0,1\}^{2^m}$ be the circuit that maps the description of a Boolean circuit with $s$ gates on $m$ inputs to its truth table. For $s = 2^m/(cm)$ with a suitable constant $c$, $\mathrm{TT}_s$ has stretch, it has size $\operatorname{poly}(2^m)$, and every non-output of $\mathrm{TT}_s$ is the truth table of a function on $m$ bits of circuit complexity greater than $s$. Consequently, an $\mathrm{FP}^{\mathrm{NP}}$ algorithm for $\mathrm{Avoid}$ (for general circuits, on infinitely many lengths) implies that $\mathrm{E}^{\mathrm{NP}}$ requires circuits of size $2^n/(cn)$ (on infinitely many lengths). Explicit constructions of rigid matrices, Ramsey graphs, two-source extractors and strings of maximum $\mathrm{K}^{\mathrm{poly}}$ complexity reduce to $\mathrm{Avoid}$ ([Probabilistic-method explicit constructions reduce to Avoid](../../complexity-classes/tfnp-hierarchies-and-avoidance/range-avoidance-and-explicit-constructions/explicit-constructions-in-apepp.md)), and conversely $\mathrm{Avoid}$ reduces under $\mathrm{P}^{\mathrm{NP}}$ reductions to constructing hard truth tables ([Korten: constructing a hard truth table is APEPP-complete under P^NP reductions](../../complexity-classes/tfnp-hierarchies-and-avoidance/range-avoidance-and-explicit-constructions/korten-hard-truth-table-apepp-complete.md)).

## Proof sketch

The number of circuits with $s$ gates is $2^{O(s \log s)} < 2^{2^m}$ for $s = 2^m/(cm)$, so $\mathrm{TT}_s$ is a stretching map, evaluating circuits is polynomial in $2^m$, and its range consists exactly of truth tables of small circuits. Running the $\mathrm{Avoid}$ algorithm on $\mathrm{TT}_s$ for input length $m = n$ computes a hard truth table in time $2^{O(n)}$ with an $\mathrm{NP}$ oracle, and the $\mathrm{E}^{\mathrm{NP}}$ language is ``output bit $x$ of that truth table''. The reductions of explicit constructions to $\mathrm{Avoid}$ build the stretching circuit from the verifier of each explicit object.

## Depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](../../complexity-classes/tfnp-hierarchies-and-avoidance/range-avoidance-and-explicit-constructions/range-avoidance-problem.md)

## Proof depends on

- [Shannon: most Boolean functions need exponential circuits](../shannon-s-circuit-size-lower-bound/shannon-hard-function.md)

## Sources

- O. Korten, "The hardest explicit construction", FOCS (2021), arXiv:2106.00875.
- R. Kleinberg, O. Korten, D. Mitropolsky, C. Papadimitriou, "Total functions in the polynomial hierarchy", ITCS (2021), LIPIcs vol. 185, paper 44.
