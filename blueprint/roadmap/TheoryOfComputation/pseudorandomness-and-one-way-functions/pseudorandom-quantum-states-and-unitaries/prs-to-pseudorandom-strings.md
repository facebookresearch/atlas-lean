# From pseudorandom states with logarithmic output length to classical pseudorandom strings

Pseudorandom quantum states with output length $n=O(\log\lambda)$ qubits (PRS on few qubits, also called short PRS) imply quantum pseudorandom *generators* with classical outputs (efficiently samplable distributions over strings, possibly with inefficient-to-describe but quantum-samplable outputs, that are computationally indistinguishable from uniform yet statistically far from it), and hence quantum commitments; by contrast, for output length $n\ge(1+\epsilon)\lambda$ no black-box reduction of this kind is known, and in fact PRS cannot be black-box shrunk to fewer qubits in general.

## Proof sketch

With logarithmically many qubits, polynomially many copies suffice for full tomography with inverse-polynomial accuracy, so measuring copies in random bases yields classical strings whose distribution can be shown pseudorandom by reducing to the PRS's pseudorandomness, while their entropy deficiency gives statistical distance from uniform. For long outputs, tomography is infeasible, and oracle separations show black-box shrinking fails.

## Depends on

- [Pseudorandom quantum state generators](pseudorandom-quantum-states.md)

## Sources

- Prabhanjan Ananth, Yao-Ting Lin, Henry Yuen, "Pseudorandom Strings from Pseudorandom Quantum States", ITCS (2024), IACR ePrint 2023/904.
