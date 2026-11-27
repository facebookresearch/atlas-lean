# Reversible quantum realization of Boolean circuit samplers

Let $C$ be a De Morgan circuit with $n$ inputs and $m$ outputs, viewed as a sampler on uniform inputs. There is a circuit of Toffoli gates $U$ mapping $|z\rangle|0\rangle \mapsto |z\rangle|C(z)\rangle$ for every $z \in \{0,1\}^n$; applying $U$ after $n$ Hadamard gates on the input register gives the state $2^{-n/2}\sum_{z}|z\rangle|C(z)\rangle$, and measuring it in the computational basis yields a uniformly random $z$ together with $C(z)$. Hence measuring the last $m$ qubits yields exactly the output distribution of $C$.

## Proof sketch

Toffoli gates with auxiliary wires fixed to constants implement AND and NOT, so $C$ is compiled gate by gate into a reversible circuit; since the computation permutes basis states, the uniform superposition over inputs is mapped to the uniform superposition over pairs $(z, C(z))$, whose measured output block has the distribution of $C$ on uniform inputs.

Derived resource count (not stated in the cited sources): if $C$ has $s$ gates, compiling into fresh ancillas (keeping garbage) and copying the outputs into a fresh block uses $n+O(s)+m$ qubits, $n$ Hadamard gates, at most $3s$ reversible gates for the Boolean gates and $m$ CNOT copies.

## Depends on

- [Quantum circuits over the Hadamard–Toffoli gate set](hadamard-toffoli-quantum-circuits.md)
- [Circuit samplers and output distributions](../../../circuit-complexity/circuit-models-synthesis-and-lower-bounds/circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-samplers-and-output-distributions.md)
- [Reversible simulation of classical circuits](../reversible-simulation-of-classical-circuits.md)

## Sources

- Ronald de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415 (version 6), Section 2.2 (Toffoli gates are complete for classical reversible computation) and Section 2.3 ("Quantum parallelism": a Toffoli circuit $U$ with $|z\rangle|0\rangle \mapsto |z\rangle|f(z)\rangle$ applied to a uniform superposition built with $n$ Hadamard transforms; observing it "will give just one uniformly random $|z\rangle|f(z)\rangle$").
- John Watrous, "Quantum Computational Complexity", in Encyclopedia of Complexity and Systems Science, Springer, 7174–7201, 2009 (arXiv:0804.3401).
- Michael A. Nielsen and Isaac L. Chuang, "Quantum Computation and Quantum Information", Cambridge University Press, 2000, Section 3.2.5 (reversible computation).
