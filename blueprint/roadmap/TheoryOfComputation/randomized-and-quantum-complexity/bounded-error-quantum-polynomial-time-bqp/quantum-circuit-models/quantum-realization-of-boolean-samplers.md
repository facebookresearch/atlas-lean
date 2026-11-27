# Reversible quantum realization of Boolean circuit samplers

Let $C$ be a De Morgan circuit with $n$ inputs, $s$ gates and $m$ outputs, viewed as a sampler on uniform inputs. There is a Hadamard–Toffoli circuit on $n+O(s)+m$ qubits, with $n$ Hadamard gates, at most $3s$ reversible gates for the Boolean gates and $m$ CNOT copies, such that measuring its last $m$ qubits in the computational basis yields exactly the output distribution of $C$.

## Proof sketch

Prepare $n$ uniform seed bits with Hadamards, compile $C$ reversibly into fresh ancillas (keeping garbage), and copy the outputs into a fresh block; since the computation is a permutation of basis states applied to a uniform superposition, the measured block has the distribution of $C$ on uniform inputs.

## Depends on

- [Quantum circuits over the Hadamard–Toffoli gate set](hadamard-toffoli-quantum-circuits.md)
- [Circuit samplers and output distributions](../../../circuit-complexity/circuit-models-synthesis-and-lower-bounds/circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-samplers-and-output-distributions.md)
- [Reversible simulation of classical circuits](../reversible-simulation-of-classical-circuits.md)

## Sources

- John Watrous, "Quantum Computational Complexity", in Encyclopedia of Complexity and Systems Science, Springer, 7174–7201, 2009 (arXiv:0804.3401).
- Michael A. Nielsen and Isaac L. Chuang, "Quantum Computation and Quantum Information", Cambridge University Press, 2000, Section 3.2.5 (reversible computation).
- Ronald de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019 (lecture notes; supplementary pointer).
