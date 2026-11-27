# Bounded-error quantum polynomial time is independent of the universal gate set

Let $\mathcal{G}, \mathcal{G}'$ be universal gate sets on a constant number of qubits whose entries are computable to $k$ bits in time $\mathrm{poly}(k)$. Every circuit of $T$ gates from $\mathcal{G}$ can be simulated, with total error $\varepsilon$ in operator norm, by a circuit of $T \cdot \mathrm{polylog}(T/\varepsilon)$ gates from $\mathcal{G}'$ computable in time $T \cdot \mathrm{polylog}(T/\varepsilon)$. Hence $\mathrm{BQP}$ defined with respect to $\mathcal{G}$ equals $\mathrm{BQP}$ defined with respect to $\mathcal{G}'$.

## Proof sketch

Approximate each gate within $\varepsilon/T$ by Solovay-Kitaev; errors of approximate gates add up by the triangle inequality and unitary invariance of the operator norm, so the total error is at most $\varepsilon$, preserving bounded acceptance gaps.

## Depends on

- [BQP](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/bqp.md)
- [Dense inverse-closed gate sets and epsilon-nets in SU(d)](dense-gate-sets-and-epsilon-nets.md)

## Proof depends on

- [Solovay-Kitaev theorem](solovay-kitaev-theorem.md)

## Sources

- Christopher M. Dawson, Michael A. Nielsen, "The Solovay-Kitaev algorithm", Quantum Information and Computation 6(1) (2006); arXiv:quant-ph/0505030.
- Alexei Kitaev, Alexander Shen, Mikhail Vyalyi, "Classical and Quantum Computation", Graduate Studies in Mathematics 47, AMS (2002).
