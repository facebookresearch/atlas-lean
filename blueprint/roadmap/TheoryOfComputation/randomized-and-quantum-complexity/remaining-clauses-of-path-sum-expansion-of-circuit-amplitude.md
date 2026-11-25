# Acceptance probabilities of Gaussian-rational circuits as GapP ratios

The path-sum identity for amplitudes is a separate page, listed under the proof dependencies. This node collects the
counting-class representation it does not state.

## Expansion

A sound expansion has separate pages for:

1. **Model.** Polynomial-time computable families $x \mapsto C_x$ of polynomial-size circuits in the encoded gate model of the
   BQP definition, whose gates have Gaussian-rational entries with polynomially many bits; $D(x)$ is the product, over the
   gates of $C_x$, of a common denominator of the real and imaginary parts of the gate's entries, so that $D$ is
   polynomial-time computable with positive integer values.
2. **Gap-function representation.** For such a family there is a function $f$ in GapP (differences of two $\#P$
   functions) such that the acceptance probability of $C_x$ on its initial state equals $f(x)/D(x)^2$ for every $x$: each
   amplitude is $(A + iB)/D(x)$ with $A$ and $B$ sums over paths of polynomial-time computable integers.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: GapP functions (closure of $\#P$ under subtraction) and their closure under exponential sums and products.

## Depends on

- [BQP](../complexity-classes/time-and-space-complexity-classes/bqp.md)
- [Acceptance probability of a quantum state](../complexity-classes/time-and-space-complexity-classes/accept-prob.md)
- [The counting class $\#P$](../complexity-classes/time-and-space-complexity-classes/sharp-p.md)

## Proof depends on

- [Path-sum expansion of quantum circuit amplitudes](path-sum-expansion-of-quantum-circuit-amplitudes.md)

## Sources

- L. Fortnow and J. Rogers, "Complexity limitations on quantum computation", arXiv:cs/9811023, Lemma 3.2 (for a polynomial-time quantum Turing machine with amplitudes $w/5$, $|w| \le 5$, the acceptance probability is $f(x)/5^{2t(|x|)}$ with $f$ in GapP) and Theorem 2.2 (closure properties of GapP); the same path-sum argument gives the Gaussian-rational case. <https://arxiv.org/abs/cs/9811023>
- S. Aaronson, MIT 6.845 Quantum Complexity Theory, Lecture 4 (scribe notes), §2.5–2.6 (BQP ⊆ P$^{\#P}$ and BQP ⊆ PP via sums over paths, informal). <https://old.ocw.mit.edu/courses/electrical-engineering-and-computer-science/6-845-quantum-complexity-theory-fall-2010/lecture-notes/MIT6_845F10_lec04.pdf>
