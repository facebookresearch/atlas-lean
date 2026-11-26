# Errors of approximate gates add up

If unitaries $U_1,\dots,U_m$ and $V_1,\dots,V_m$ act on the same space, then $\|U_m\cdots U_1-V_m\cdots V_1\|\le\sum_{i=1}^m\|U_i-V_i\|$ in operator norm. The same holds when whole subcircuits are replaced, and the final states (and hence measurement probabilities, up to a factor two in total variation) move by at most the same amount. This is how circuits over one gate set are compiled into another up to small error.

## Proof sketch

Telescoping: $U_m\cdots U_1-V_m\cdots V_1=\sum_iU_m\cdots U_{i+1}(U_i-V_i)V_{i-1}\cdots V_1$ and unitaries have norm one.

## Depends on

- [Quantum circuits over the Hadamard–Toffoli gate set](hadamard-toffoli-quantum-circuits.md)

## Sources

- Ronald de Wolf, "Quantum Computing: Lecture Notes", 2019.
- A. Yu. Kitaev, "Quantum Computations: Algorithms and Error Correction", Russian Mathematical Surveys, 1997.
