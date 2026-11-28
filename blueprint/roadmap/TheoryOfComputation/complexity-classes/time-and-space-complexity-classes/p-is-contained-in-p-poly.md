# P is contained in P/poly

**Theorem.** A language has logspace-uniform Boolean circuit families of polynomial size if and only if it is in $\mathsf{P}$. In particular $\mathsf{P} \subseteq \mathsf{P/poly}$.

The "only if" direction evaluates the circuit generated in logarithmic space. For the "if" direction, a machine running in time $T(n)$ is simulated by an oblivious
machine, whose head movements do not depend on the input, in time $O(T(n)^2)$, and the snapshots of the oblivious computation are computed by a circuit whose
structure is the same for all inputs of length $n$ and can be generated in logarithmic space, as in the proof of the Cook–Levin theorem.

## Depends on

- [Polynomial time with polynomial advice](ppoly.md)

## Proof depends on

- [Oblivious simulation of a Turing machine in quadratic time](../../turing-machines/multi-tape-and-multi-stack/oblivious-simulation-in-quadratic-time.md)

## Expansion

This page becomes ready once:

- Logspace-uniform circuit families in the source's sense, described by the functions SIZE, TYPE and EDGE of the adjacency-matrix representation and computed implicitly in logarithmic space (statement prerequisite; not yet stated). The existing [log-space uniform circuit families](uniform-circuit-family.md) uses gate lists written by a log-space transducer; relating the two representations is part of this item.
- A logarithmic-space head schedule for the construction: for a time-constructible polynomial running-time bound $T(n) \ge n$, the quadratic oblivious simulation can be chosen so that, from $n$ and $i$, the position of each head at step $i$ on inputs of length $n$ is computable in space $O(\log T(n))$ (proof prerequisite; not yet stated). This is a property of the construction, not a consequence of obliviousness alone.
- Snapshot circuits for such a polynomial-time machine: there are circuits $C_n$, one constant-size block per step and a final constant-size block testing for an accepting snapshot, with $C_n(x)$ equal to the machine's output for every $x$ of length $n$, and every bit of the description of $C_n$ is computable in logarithmic space (proof prerequisite; not yet stated).
- Evaluation for the converse: a logspace-uniform family of polynomial-size circuits decides a language in polynomial time, including polynomial-time generation of the implicitly logspace-computable description of $C_n$ and evaluation gate by gate (proof prerequisite; not yet stated). The existing [Circuit Value Problem is P-complete](../../completeness-other-classes/circuit-value-problem/cvp-p-complete.md) states membership in P for the repository's gate-list encoding and canonical P; using it here needs the same representation and machine-model agreement.

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, <https://theory.cs.princeton.edu/complexity/>: Definition 6.5 (logspace-uniform circuit families), Remark 6.6 (circuit representations), Theorem 6.7 with its proof sketch, and Remark 6.8.
