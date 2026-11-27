# Exactly unitary Gaussian-rational approximations of 1- and 2-qubit gates

This node collects the existence of exactly unitary matrices with Gaussian-rational entries close to given one- and
two-qubit gates.

## Expansion

A sound expansion has separate pages for:

1. **Density with bit-length.** For every $U \in U(2)$ (in particular the Hadamard gate and the phases
   $e^{2\pi i/2^k}$) and every $\varepsilon \in (0,1)$ there is a unitary with entries in $\mathbb{Q}(i)$ within $\varepsilon$ of
   $U$ in operator norm, with entries of bit-length $O(\log(1/\varepsilon))$; likewise for controlled phases
   $\mathrm{diag}(1,1,1,e^{i\theta})$. One proof uses rational points on spheres by stereographic projection from a pole
   chosen away from the target; that argument is a derivation, not a statement of the cited notes.
2. **Snapping and generation,** computing such a matrix from numerical data and its running time, are separate
   nodes.

## Depends on

- [Unitary evolution and elementary gates](../../../QuantumInformation/quantum-foundations/unitary-evolution-and-elementary-gates.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §2.2 (approximate universality of gate sets; background, not a statement of this construction). <https://arxiv.org/pdf/1907.09415v6>
