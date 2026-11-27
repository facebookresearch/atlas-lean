# BQP form of the sign lemma

Every language `L` in `BQP` has a polynomial-time computable
family of circuits of well-formed gates (unitary 2-local gates, `QGateWellFormed`), with
polynomially many ancilla qubits and gates, such that for every input `x` the path-pair gap of
the circuit for `x`, for paths from the initial index of `x`, is positive exactly when `L x` is
true.
