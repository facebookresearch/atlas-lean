# Valiant's universality: every polynomial is a projection of a generic determinant

Over every field $F$, every polynomial $f \in F[x_1,\dots,x_N]$ is a projection of the generic $m\times m$ determinant for some $m$. In particular every polynomial has finite determinantal complexity, and $\mathrm{dc}(f)$ is attained by some finite matrix.

## Proof sketch

Every polynomial is computed by some arithmetic formula (a sum of monomials), and formulas are projections of determinants of size one more than their number of operation gates, so $\mathrm{dc}(f)$ is at most one more than the formula size of $f$.

## Depends on

- [Specialization matrices and determinantal representations](specialization-matrices-and-determinantal-representations.md)

## Proof depends on

- [Valiant: arithmetic formulas are projections of linear-size determinants](formulas-are-projections-of-determinants.md)

## Sources

- Leslie G. Valiant, "Completeness Classes in Algebra", Proceedings of the Eleventh Annual ACM Symposium on Theory of Computing, 1979.
- Peter Bürgisser, "Completeness classes in algebraic complexity theory", in Foundations of Computation and Machine Learning: The Work of Leslie Valiant, ACM; arXiv:2406.06217, 2024, Section 2.9 (Definition 2.35 and the remark after it: Proposition 2.23 shows $\mathrm{dc}(f) \le E(f) + 1$, so $\mathrm{dc}(f)$ is finite).
- Ramprasad Saptharishi, "A survey of lower bounds in arithmetic circuit complexity", version 9.0.3, 2021.
