# Trace distance: metric, operational form and contractivity

The trace distance $T(\rho, \sigma) = \tfrac12 \lVert \rho - \sigma \rVert_1$, its expression through absolute eigenvalues, its
nonnegativity, its symmetry and its bound by $1$ are separate results and are not part of this node. This node collects the remaining clauses.

## Expansion

A sound expansion has separate pages for:

1. **Metric.** The trace distance is a metric on density operators (triangle inequality and definiteness).
2. **Operational form.** $T(\rho, \sigma) = \max_P \mathrm{Tr}(P(\rho - \sigma))$ over projections $P$, equivalently over operators
   $0 \le P \le I$; with equal priors this is the largest bias $2p_{\mathrm{succ}} - 1$ with which a measurement distinguishes
   the two states, the case $\lambda = 1/2$ of the Holevo–Helstrom theorem.
3. **Contractivity.** $T(\Phi(\rho), \Phi(\sigma)) \le T(\rho, \sigma)$ for every channel $\Phi$, and more generally for every
   positive trace-preserving map.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Quantum channels (CPTP maps).

## Related topics

- [Holevo–Helstrom theorem](../quantum-operations/holevohelstrom-theorem.md)

## Sources

- J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018 (author copy), Section 1.1.3 (the trace norm is a norm), Theorem 3.4 (Holevo–Helstrom) and Corollary 3.40 with the remark after it ($\lVert \Phi(X) \rVert_1 \le \lVert X \rVert_1$ for positive trace-preserving $\Phi$). <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>
- M. M. Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Lemma 9.1.1 ($\tfrac12\lVert\rho - \sigma\rVert_1 = \max_{0 \le \Lambda \le I} \mathrm{Tr}\{\Lambda(\rho - \sigma)\}$), Lemma 9.1.2 (triangle inequality) and Exercise 9.1.9 (monotonicity under channels). <https://arxiv.org/abs/1106.1445>
