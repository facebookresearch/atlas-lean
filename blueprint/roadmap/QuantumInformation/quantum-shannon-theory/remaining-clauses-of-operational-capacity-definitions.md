# Operational classical and quantum capacities

For a channel $\Phi$ between finite-dimensional spaces, a rate $R \ge 0$ is achievable for classical communication if for
every $\varepsilon > 0$ there is $n_0$ such that for every $n \ge n_0$ there are an encoding of $2^{\lfloor Rn \rfloor}$ messages into
input states of $\Phi^{\otimes n}$ and a measurement decoding them with maximal error probability below $\varepsilon$. The
(unassisted) classical capacity $C(\Phi)$ is the supremum of achievable rates.

A rate $R \ge 0$ is achievable for quantum communication if for every $\varepsilon > 0$ and all but finitely many $n$ there
are channels $\Xi_E$ from $\lfloor Rn \rfloor$ qubits to the input of $\Phi^{\otimes n}$ and $\Xi_D$ from its output to
$\lfloor Rn \rfloor$ qubits with $\lVert \Xi_D \Phi^{\otimes n} \Xi_E - \mathrm{id} \rVert_\diamond < \varepsilon$, where $\lVert \cdot \rVert_\diamond$ is the
completely bounded trace norm. The (unassisted) quantum capacity $Q(\Phi)$ is the supremum of these rates.

## Expansion

This node states a precise definition. A good expansion adds a page for each pending prerequisite below and links it
under the dependency sections.

- Statement prerequisite: Quantum channels (CPTP maps).
- Statement prerequisite: Measurements (POVMs).
- Statement prerequisite: The completely bounded trace norm of a linear map.

## Sources

- J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018 (author copy), Definitions 8.1–8.3
  with (8.3)–(8.6) (classical capacity; per-message error below $\varepsilon/2$ is equivalent) and Definition 8.42 (quantum
  capacity). <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>
