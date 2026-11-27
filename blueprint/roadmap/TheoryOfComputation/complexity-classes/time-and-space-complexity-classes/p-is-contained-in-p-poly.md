# P is contained in P/poly

**Theorem.** A language has logspace-uniform Boolean circuit families of polynomial size if and only if it is in $\mathsf{P}$. In particular $\mathsf{P} \subseteq \mathsf{P/poly}$.

The "only if" direction evaluates the circuit generated in logarithmic space. For the "if" direction, a machine running in time $T(n)$ is simulated by an oblivious
machine, whose head movements do not depend on the input, in time $O(T(n)^2)$, and the snapshots of the oblivious computation are computed by a circuit whose
structure is the same for all inputs of length $n$ and can be generated in logarithmic space, as in the proof of the Cook–Levin theorem.

## Depends on

- [Polynomial time with polynomial advice](ppoly.md)

## Expansion

This page becomes ready once:

- Logspace-uniform circuit families (statement prerequisite; not yet stated)
- Simulation of a time-$T(n)$ Turing machine by an oblivious machine in time $O(T(n)^2)$ (proof prerequisite; not yet stated)

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, <https://theory.cs.princeton.edu/complexity/>: Definition 6.5 (logspace-uniform circuit families), Theorem 6.7 with its proof sketch, and Remark 6.8.
