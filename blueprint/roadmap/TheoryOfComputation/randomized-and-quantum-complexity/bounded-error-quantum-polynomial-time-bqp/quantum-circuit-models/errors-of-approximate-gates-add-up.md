# Errors of approximate gates add up

Let $U_1,\dots,U_m$ and $V_1,\dots,V_m$ be unitaries on the same space, possibly whole subcircuits, and let $\eta=\sum_{i=1}^m\|U_i-V_i\|$ in operator norm, so that $\|U_m\cdots U_1-V_m\cdots V_1\|\le\eta$ by the telescoping bound for products of contractions (unitaries have norm $1$). Then for every unit vector $\psi$ the final states $U_m\cdots U_1\psi$ and $V_m\cdots V_1\psi$ are at Euclidean distance at most $\eta$, and their computational-basis measurement distributions are at $\ell_1$ distance at most $2\eta$, i.e. total variation distance at most $\eta$. This is how circuits over one gate set are compiled into another up to small error.

## Proof sketch

The operator-norm bound gives the bound on states. For unit vectors $\psi,\varphi$, $\sum_x\bigl||\psi_x|^2-|\varphi_x|^2\bigr|\le\sum_x|\psi_x-\varphi_x|(|\psi_x|+|\varphi_x|)\le2\|\psi-\varphi\|$ by Cauchy–Schwarz.

## Depends on

- [Quantum circuits over the Hadamard–Toffoli gate set](hadamard-toffoli-quantum-circuits.md)
- [Telescoping bound for products of contractions](../../../../QuantumInformation/not-yet-classified/part-01/unitary-error-budget/norm-list-of-fn-prod-sub-le.md)

## Sources

- Michael A. Nielsen and Isaac L. Chuang, "Quantum Computation and Quantum Information", Cambridge University Press, 2000, Section 4.5.3.
- Ethan Bernstein and Umesh Vazirani, "Quantum Complexity Theory", SIAM Journal on Computing 26(5), 1411–1473, 1997.
- Ronald de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019 (lecture notes; supplementary pointer).
- A. Yu. Kitaev, "Quantum Computations: Algorithms and Error Correction", Russian Mathematical Surveys 52(6), 1191–1249, 1997.
