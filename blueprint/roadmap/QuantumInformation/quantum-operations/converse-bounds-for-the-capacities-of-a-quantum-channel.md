# Converse bounds for the capacities of a quantum channel

Let $\Phi$ be a quantum channel with classical capacity $C(\Phi)$, defined operationally, and let $\chi(\Phi)$ be the
maximum over ensembles $\eta$ of the Holevo quantity of $\Phi(\eta)$. Then

$$C(\Phi) \le \lim_{n \to \infty} \frac{\chi(\Phi^{\otimes n})}{n}.$$

(The Holevo–Schumacher–Westmoreland theorem states that this inequality is an equality.)

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Quantum channels (CPTP maps).
- Statement prerequisite: Operational definitions of channel capacities.
- Proof prerequisite: Fano's inequality for joint distributions with zero-probability outcomes (the linked version assumes strictly positive probabilities).

## Proof depends on

- [Holevo's theorem](../quantum-shannon-theory/holevo-s-theorem.md)
- [Fano's inequality, general form](../../InformationTheory/information-inequalities/fano-s-inequality/fano-inequality-general.md)
- [Fannes–Audenaert inequality](../quantum-states-distances-and-entropy/fannesaudenaert-inequality.md)

## Sources

- J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018 (author copy), §8.1.1–8.1.2 and Theorem 8.27 (converse part). <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>
