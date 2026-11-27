# BQP error reduction

Let $L \in \mathsf{BQP}$ be decided, in the encoded gate model of the BQP definition, by a polynomial-time computable
family of polynomial-size circuits with error at most $1/3$, and let $p$ be a polynomial. There is a polynomial-time
computable family of polynomial-size circuits in the same model that decides $L$ with error at most $2^{-p(n)}$: it
copies the input by CNOT gates into $k$ fresh blocks, for the least odd $k \ge 18 \ln 2 \cdot (p(n) + 1)$, runs the original
circuit on each block with its own ancilla qubits initialized to $0$, computes the majority of the $k$ output qubits into a
fresh qubit by a reversible circuit, and swaps that qubit into the measured output qubit $0$. The $k$ output bits are
independent, each correct with probability at least $2/3$, so by Hoeffding's inequality the majority errs with probability
at most $2 e^{-k/18} \le 2^{-p(n)}$.

## Depends on

- [BQP](../complexity-classes/time-and-space-complexity-classes/bqp.md)
- [Applying a 2-local gate to a state](../complexity-classes/time-and-space-complexity-classes/apply-gate.md)

## Proof depends on

- [Reversible simulation of classical circuits](bounded-error-quantum-polynomial-time-bqp/reversible-simulation-of-classical-circuits.md)
- [Exact Gaussian-rational Toffoli and multi-controlled NOT decompositions](bounded-error-quantum-polynomial-time-bqp/exact-2-local-gaussian-rational-toffoli-and-multi-controlled.md)

## Sources

- J. Watrous, "Quantum computational complexity", arXiv:0804.3401, Section IV.2, Proposition 3 (error reduction for BQP, by repetition). <https://arxiv.org/abs/0804.3401>
- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §13.2 (majority of $O(\log(1/\varepsilon))$ runs) and Appendix B.2 (Chernoff/Hoeffding bound $\Pr[|X - \mu| \ge \alpha n] \le 2e^{-2\alpha^2 n}$). <https://arxiv.org/pdf/1907.09415v6>
- S. Aaronson, MIT 6.845 Quantum Complexity Theory, Lecture 4 (scribe notes), §4.2 (majority vote over parallel runs, informal). <https://old.ocw.mit.edu/courses/electrical-engineering-and-computer-science/6-845-quantum-complexity-theory-fall-2010/lecture-notes/MIT6_845F10_lec04.pdf>
