# Feasible instances of SATISFIABILITY OF QUADRATIC EQUATIONS OVER GF(q)

An instance $(q, n, P, K)$ is feasible when there are a set $S$ of positions in the list $P$ with $|S| \ge K$ and a point $x \in (\mathbb{Z}/q\mathbb{Z})^n$ at which every polynomial at a position in $S$ vanishes. Each polynomial is read from its list of terms (coefficient, variable-index list) as a polynomial over $\mathbb{Z}/q\mathbb{Z}$, coefficients taken modulo $q$, and evaluated there.

This predicate counts positions in the list and does not itself require $q$ to be prime or the listed polynomials to be distinct; those conditions belong to [well-formedness](well-formed-17.md), which the [decision problem](quadratic-equations-dec.md) checks separately. For a well-formed instance, $\mathbb{Z}/q\mathbb{Z}$ is the field $\mathrm{GF}(q)$ and distinct positions carry distinct polynomials, so feasibility says that at least $K$ distinct polynomials of $P$ have a common zero in $\mathrm{GF}(q)^n$.
