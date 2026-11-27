# Local stochastic error model

Let $C$ be a quantum circuit with [locations](locations-of-a-quantum-circuit.md) $C_i$, and fix numbers $p_i < 1$. An error
model on $C$ is local stochastic with bounds $p_i$ if, with some probability $p_S$, faults occur at exactly the set $S$ of
locations, in which case the operations at those locations are replaced by arbitrary quantum operations consistent with
the causal order of $S$ (possibly correlated with each other), and for every set $R$ of locations

$$\sum_{S \supseteq R} p_S \;\le\; \prod_{i \in R} p_i .$$

When all $p_i = p$, faults at $r$ given locations occur together with probability at most $p^r$; what happens elsewhere
is unconstrained. If the set of faulty locations is random with each location faulty independently with probability $p_i$,
the model is local stochastic whatever operations act at the faulty locations, since then
$\sum_{S \supseteq R} p_S = \prod_{i \in R} p_i$; Gottesman's uncorrelated model, in which in addition the error operation
at each faulty location is drawn independently of the others, is a special case. The model is preserved by the level reduction of concatenated fault-tolerant circuits, which is
why the threshold theorem is stated for it.

## Depends on

- [Locations of a quantum circuit](locations-of-a-quantum-circuit.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 5.2, Definitions 11 and 12.
