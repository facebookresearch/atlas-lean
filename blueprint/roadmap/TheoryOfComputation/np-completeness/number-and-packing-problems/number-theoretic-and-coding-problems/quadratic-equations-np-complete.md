# SATISFIABILITY OF QUADRATIC EQUATIONS OVER GF(q) is NP-complete

The [decision problem](quadratic-equations-dec.md) SATISFIABILITY OF QUADRATIC EQUATIONS OVER GF(q) belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Its input carries the prime $q$ and the threshold $K$ as numbers, together with $n$ and a list $P$ of polynomials over $\mathrm{GF}(q)$ in $x_1, \dots, x_n$ of degree at most $2$ with no square monomial $x_i^2$; an instance is accepted when it is [well-formed](well-formed-17.md) (in particular $q$ is prime and the listed polynomials are pairwise distinct) and at least $K$ of the listed polynomials have a common zero in $\mathrm{GF}(q)^n$.

Membership in NP: a certificate is an assignment $x \in \mathrm{GF}(q)^n$, and the verifier evaluates every polynomial at $x$ and checks that at least $K$ of them vanish. Hardness comes from a special case: for one fixed prime $p$, deciding whether all the polynomials of an instance have a common zero (the instances with $q = p$ and $K$ equal to the number of polynomials) is already NP-complete. That result concerns this special case only, not the threshold problem with $q$ and $K$ in the input.

## Sources

- P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem MAXIMUM SATISFIABILITY OF QUADRATIC EQUATIONS OVER GF[Q] (decision version), the problem stated here.
- J. Håstad, S. Phillips and S. Safra, "A well-characterized approximation problem", Information Processing Letters 47 (1993), 301-305, doi:10.1016/0020-0190(93)90076-L, Theorem 4.2: for every fixed prime $p$, deciding whether all equations of an instance can be satisfied simultaneously is NP-complete (the special case above).
