# Quantum oracle circuits with coherent XOR queries

For a function $H:\{0,1\}^a\to\{0,1\}^b$, the *coherent XOR query* on designated wires $A$ (the first $a$ holding the argument and the next $b$ the accumulator) is the unitary $|x,y,z\rangle\mapsto|x,y\oplus H(x),z\rangle$, acting as the identity on all other wires $z$. A *quantum oracle circuit* is a gate list mixing elementary gates and XOR queries to a fixed oracle; its resources are the register width, the number of elementary gates, the number of oracle queries and the description length, bounded separately. A random oracle samples $H$ uniformly once per execution.

## Depends on

- [Quantum circuits over the Hadamard–Toffoli gate set](hadamard-toffoli-quantum-circuits.md)
- [Phase oracle](../../../../ComputerScience/quantum-algorithms/grover-s-algorithm/phase-oracle.md)

## Sources

- Charles H. Bennett, Ethan Bernstein, Gilles Brassard, Umesh Vazirani, "Strengths and Weaknesses of Quantum Computing", SIAM Journal on Computing 26(5), 1510–1523, 1997.
- Dan Boneh, Özgür Dagdelen, Marc Fischlin, Anja Lehmann, Christian Schaffner and Mark Zhandry, "Random Oracles in a Quantum World", Advances in Cryptology – ASIACRYPT 2011, Lecture Notes in Computer Science 7073, 41–69, 2011.
- Michael A. Nielsen and Isaac L. Chuang, "Quantum Computation and Quantum Information", Cambridge University Press, 2000, Section 6.1.
- Ronald de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019 (lecture notes; supplementary pointer).
