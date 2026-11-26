# Termination of DPLL modulo theories

Let $F$ be a finite set of ground clauses. A derivation $\emptyset \parallel F = S_0 \Longrightarrow_{\mathcal{FT}} S_1 \Longrightarrow_{\mathcal{FT}} \cdots$ in the [full DPLL modulo theories system](dpll-modulo-theories-transition-system.md) is finite if:

1. it has no infinite subderivation consisting only of T-Learn and T-Forget steps; and
2. for every subderivation $S_{i-1} \Longrightarrow S_i \Longrightarrow \cdots \Longrightarrow S_j \Longrightarrow \cdots \Longrightarrow S_k$ whose only Restart steps are the ones producing $S_i$, $S_j$ and $S_k$, either there are more Basic DPLL modulo theories steps from $S_j$ to $S_k$ than from $S_i$ to $S_j$, or a clause learned between $S_j$ and $S_k$ is never forgotten in the derivation. Here a clause is *learned* by a T-Learn step only if it did not already belong to the clause set; T-Learn steps that add a clause already present do not count. Without this convention the criterion fails: from $F = \{p \vee q\}$, repeatedly deciding $p$, applying T-Learn to $p \vee q$ and restarting never forgets a clause and never terminates.

## Depends on

- [DPLL modulo theories transition system](dpll-modulo-theories-transition-system.md)

## Proof depends on

- [Invariants of DPLL modulo theories](invariants-of-dpll-modulo-theories.md)
- [Termination of abstract DPLL with learning](../../../Logic/propositional-logic/sat-solving/termination-of-abstract-dpll-with-learning.md)

## Sources

- R. Nieuwenhuis, A. Oliveras and C. Tinelli, "Solving SAT and SAT modulo theories: from an abstract Davis–Putnam–Logemann–Loveland procedure to DPLL(T)", *Journal of the ACM* 53(6):937–977, 2006, <https://www.cs.upc.edu/~roberto/papers/JACM2006.pdf>, Section 3.4, Theorem 3.7 and its proof, an extension of the proof of Theorem 2.16, with footnote 2 referring to Definition 2.5 for when a clause is learned.
