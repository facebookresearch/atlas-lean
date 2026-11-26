# Nayak's bound for quantum random access codes

Suppose $n$-bit strings $x$ are encoded into states $\rho_x$ of $m$ qubits such that, for every $i$, the bit
$x_i$ can be recovered from $\rho_x$ with success probability at least $p \ge 1/2$, averaged over uniformly random $x$ and the randomness of the measurement. Then

$$m \ge (1 - H(p))\, n,$$

where $H$ is the binary entropy function.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Proof prerequisite: Fano's inequality for joint distributions with zero-probability outcomes (the linked version assumes strictly positive probabilities).

## Proof depends on

- [Holevo's theorem](holevo-s-theorem.md)
- [Fano's inequality, general form](../../InformationTheory/information-inequalities/fano-s-inequality/fano-inequality-general.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §15.2, Theorem 4. <https://arxiv.org/pdf/1907.09415v6>
- J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018 (author copy), Theorem 5.53. <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>
