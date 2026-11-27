# Errors of approximate gates add up

If unitaries $U_1,\dots,U_m$ and $V_1,\dots,V_m$ act on the same space, then $\|U_m\cdots U_1-V_m\cdots V_1\|\le\sum_{i=1}^m\|U_i-V_i\|$ in operator norm. The same holds when whole subcircuits are replaced. The final states move by at most the same amount $\eta$ in Euclidean norm, and the computational-basis measurement distributions are then at $\ell_1$ distance at most $2\eta$, i.e. total variation distance at most $\eta$. This is how circuits over one gate set are compiled into another up to small error.

## Proof sketch

Telescoping: $U_m\cdots U_1-V_m\cdots V_1=\sum_iU_m\cdots U_{i+1}(U_i-V_i)V_{i-1}\cdots V_1$ and unitaries have norm one. For unit vectors $\psi,\varphi$, $\sum_x\bigl||\psi_x|^2-|\varphi_x|^2\bigr|\le\sum_x|\psi_x-\varphi_x|(|\psi_x|+|\varphi_x|)\le2\|\psi-\varphi\|$ by Cauchy–Schwarz.

## Depends on

- [Quantum circuits over the Hadamard–Toffoli gate set](hadamard-toffoli-quantum-circuits.md)

## Sources

- Michael A. Nielsen and Isaac L. Chuang, "Quantum Computation and Quantum Information", Cambridge University Press, 2000, Section 4.5.3.
- Ethan Bernstein and Umesh Vazirani, "Quantum Complexity Theory", SIAM Journal on Computing 26(5), 1411–1473, 1997.
- Ronald de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019 (lecture notes; supplementary pointer).
- A. Yu. Kitaev, "Quantum Computations: Algorithms and Error Correction", Russian Mathematical Surveys 52(6), 1191–1249, 1997.
