# Snapping approximate values to exact Gaussian-rational unitaries

This node collects the computation of exactly unitary Gaussian-rational matrices from approximate numerical data.

## Expansion

A sound expansion has separate pages for:

1. **Input.** Rational approximations, within $\varepsilon$, of a unit complex number or of a point of $S^3$ that parametrizes a
   target unitary.
2. **Procedure.** A well-conditioned parametrization (for example stereographic coordinates with a pole chosen away
   from the target) that maps the data to an exactly unitary matrix with entries in $\mathbb{Q}(i)$.
3. **Guarantee.** An exact rational point of $S^1$ or $S^3$, hence an exactly unitary Gaussian-rational gate, within
   $O(\varepsilon)$ of the target in operator norm, with entries of $O(\log(1/\varepsilon))$ bits, computed in polynomial time;
   density of rational unitaries alone does not give such a procedure.

## Proof depends on

- [Exactly unitary Gaussian-rational approximations of 1- and 2-qubit gates](exactly-unitary-gaussian-rational-approximations-of-1-and-2.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §2.2 (approximate universality of gate sets; background, not a statement of this procedure). <https://arxiv.org/pdf/1907.09415v6>
