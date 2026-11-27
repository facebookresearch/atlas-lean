# Moser's resampling algorithm for $k$-SAT

Let $\varphi$ be a CNF formula in which every clause has exactly $k$ literals on distinct variables. Two clauses are *neighbours* if they share a variable (each clause is its own neighbour). Moser's algorithm draws a uniformly random assignment and then, for each clause $C$ in a fixed order, calls $\mathrm{Fix}(C)$ if $C$ is violated, where $\mathrm{Fix}(C)$ resamples the $k$ variables of $C$ with fresh independent uniform bits and, while some neighbour of $C$ is violated, calls $\mathrm{Fix}(D)$ on the first violated neighbour $D$. The *degree* $d$ of $\varphi$ is the maximum number of neighbours of a clause other than itself.

## Depends on

- [CNF formula](../../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)

## Sources

- R. A. Moser, "A Constructive Proof of the Lovász Local Lemma", Proceedings of the 41st ACM Symposium on Theory of Computing (STOC), 343–350, 2009, Algorithm 2.1 (local correction with the lexicographically first violated clause of the inclusive neighbourhood; the source also restarts runs that take too long).
