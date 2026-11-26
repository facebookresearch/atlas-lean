# Final states of DPLL modulo theories

Let $\emptyset \parallel F \Longrightarrow^*_{\mathcal{FT}} S$ be a derivation in the [full DPLL modulo theories system](dpll-modulo-theories-transition-system.md) such that $S$ is final with respect to the Basic DPLL modulo theories rules and, if $S = M \parallel F'$, the assignment $M$ is $T$-consistent. Then:

1. $S$ is FailState if and only if $F$ is $T$-unsatisfiable;
2. if $S = M \parallel F'$, then $M$ is a $T$-model of $F$.

So, with a decision procedure for $T$-consistency of conjunctions of ground literals, such as a complete [theory solver](theory-solvers-for-dpll-t.md), any strategy that terminates and applies T-Learn when the assignment is $T$-inconsistent decides $T$-satisfiability.

## Depends on

- [DPLL modulo theories transition system](dpll-modulo-theories-transition-system.md)
- [Theory solvers for DPLL(T)](theory-solvers-for-dpll-t.md)

## Proof depends on

- [Termination of DPLL modulo theories](termination-of-dpll-modulo-theories.md)
- [Invariants of DPLL modulo theories](invariants-of-dpll-modulo-theories.md)
- [Conflicting clauses enable Fail or T-Backjump](conflicting-clauses-enable-fail-or-t-backjump.md)

## Sources

- R. Nieuwenhuis, A. Oliveras and C. Tinelli, "Solving SAT and SAT modulo theories: from an abstract Davis–Putnam–Logemann–Loveland procedure to DPLL(T)", *Journal of the ACM* 53(6):937–977, 2006, <https://www.cs.upc.edu/~roberto/papers/JACM2006.pdf>, Section 3.4, Theorem 3.10 and its proof, and the remarks after Property 3.9 and after Theorem 3.10.
