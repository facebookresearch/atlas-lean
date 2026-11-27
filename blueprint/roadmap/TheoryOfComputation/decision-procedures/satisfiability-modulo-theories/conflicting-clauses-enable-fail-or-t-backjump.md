# Conflicting clauses enable Fail or T-Backjump

Let $\emptyset \parallel F \Longrightarrow^*_{\mathcal{FT}} M \parallel F'$ in the [full DPLL modulo theories system](dpll-modulo-theories-transition-system.md).

1. If $M \models \neg C$ for some clause $C$ of $F'$, then Fail or T-Backjump applies to $M \parallel F'$.
2. If $M$ is $T$-inconsistent, then either $M \parallel F'$ has a conflicting clause, or T-Learn applies to it and produces one: for a subset $\{l_1, \dots, l_n\}$ of $M$ with $\models_T \neg l_1 \vee \dots \vee \neg l_n$, that clause can be learned.

## Depends on

- [DPLL modulo theories transition system](dpll-modulo-theories-transition-system.md)

## Proof depends on

- [Invariants of DPLL modulo theories](invariants-of-dpll-modulo-theories.md)

## Sources

- R. Nieuwenhuis, A. Oliveras and C. Tinelli, "Solving SAT and SAT modulo theories: from an abstract Davis–Putnam–Logemann–Loveland procedure to DPLL(T)", *Journal of the ACM* 53(6):937–977, 2006, <https://www.cs.upc.edu/~roberto/papers/JACM2006.pdf>, Section 3.4: Lemma 3.8 (proved as Lemma 2.8) and Property 3.9 with its proof.
