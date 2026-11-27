# Unions of convex theories are convex

If $T_1$ and $T_2$ are signature-disjoint first-order theories that are [convex with respect to equations](convex-theories.md) and have no trivial models, then $T_1 \cup T_2$ is convex with respect to equations and has no trivial models.

**Proof.** A trivial model of the union would be one of each component. If $T_1 \cup T_2 \models \forall \vec x\,(\Gamma \to x_1 \approx x'_1 \vee \dots \vee x_n \approx x'_n)$, run the deterministic Nelson–Oppen procedure on the purified $\Gamma \wedge \bigwedge_j x_j \not\approx x'_j$. By convexity each propagated equation follows from the positive and non-equational literals, and the final Unsat step uses at most one disequation $x_j \not\approx x'_j$, so $T_1 \cup T_2 \models \forall \vec x\,(\Gamma \to x_j \approx x'_j)$.

## Depends on

- [Convex theories](convex-theories.md)

## Proof depends on

- [Deterministic Nelson–Oppen combination for convex theories](nelson-oppen-for-convex-theories.md)

## Sources

- U. Waldmann, *Automated Reasoning II*, lecture notes, Max Planck Institute for Informatics, summer semester 2024, <https://rg1-teaching.mpi-inf.mpg.de/autrea2-ss24/notes-current.pdf>, Section 1.11, Lemma 1.13 and Theorem 1.14 with its proof, pp. 31–32.
