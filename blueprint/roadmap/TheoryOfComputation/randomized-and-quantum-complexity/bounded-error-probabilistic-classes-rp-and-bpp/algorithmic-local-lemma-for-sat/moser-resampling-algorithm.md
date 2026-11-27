# Moser's resampling algorithm for $k$-SAT

Let $\varphi$ be a CNF formula with $m$ clauses in which every clause has exactly $k$ literals on distinct variables, and fix an arbitrary global ordering of the clauses (the lexicographic order). Two clauses are *neighbours* if they share a variable (each clause is its own neighbour). The *local correction* $\mathrm{Fix}(C)$ of a violated clause $C$ resamples the $k$ variables of $C$ with fresh independent uniform bits and then, while some neighbour of $C$ is violated, calls $\mathrm{Fix}(D)$ on the lexicographically first violated neighbour $D$. *Moser's algorithm* draws a uniformly random assignment and, while some clause is violated, calls $\mathrm{Fix}(D)$ on the lexicographically first violated clause $D$, counting the recursive invocations made by this call; if their number exceeds $\log m + 2$, it aborts the whole loop and restarts from a fresh uniformly random assignment. The *degree* $d$ of $\varphi$ is the maximum number of neighbours of a clause other than itself.

## Proof sketch

Derived remark (not stated in the source in this form): since a returning call $\mathrm{Fix}(C)$ leaves $C$ satisfied and keeps every previously satisfied clause satisfied, each run of the top-level loop between restarts calls $\mathrm{Fix}$ on each clause at most once, in increasing lexicographic order; so dropping the abort rule gives the variant that, for each clause $C$ in the fixed order, calls $\mathrm{Fix}(C)$ if $C$ is violated.

## Depends on

- [CNF formula](../../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)

## Sources

- R. A. Moser, "A Constructive Proof of the Lovász Local Lemma", Proceedings of the 41st ACM Symposium on Theory of Computing (STOC), 343–350, 2009, numbering of arXiv:0810.4812, Section 2, Algorithm 2.1 (local correction with the lexicographically first violated clause of the inclusive neighbourhood) and Algorithm 2.2 (the complete solver, with abort and restart after more than $\log m + 2$ recursive invocations).
