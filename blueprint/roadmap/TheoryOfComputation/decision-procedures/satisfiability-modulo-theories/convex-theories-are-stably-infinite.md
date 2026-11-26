# Convex theories without trivial models are stably infinite

If a first-order theory $T$ is [convex with respect to equations](convex-theories.md) and has no trivial models, then $T$ is stably infinite.

**Proof.** Suppose some $T$-satisfiable conjunction of literals $\exists \vec x\, F$ has only finite $T$-models; by compactness their size is bounded by some $m$. Then $T$ entails $\forall \vec x, \vec y\,(F^+ \to \neg F^- \vee \bigvee_{1 \le i < j \le m+1} y_i \approx y_j)$, where $F^-$ collects the negative equational literals of $F$, $F^+$ the others, and $y_1, \dots, y_{m+1}$ are fresh. By convexity $T$ entails one disjunct alone. A literal of $\neg F^-$ would make $F$ unsatisfiable, and $y_i \approx y_j$ fails in any $T$-model of $\exists \vec x\, F^+$, which has at least two elements. Hence $\exists \vec x\, F$ has an infinite $T$-model.

## Depends on

- [Convex theories](convex-theories.md)

## Proof depends on

- [Compactness theorem for first-order logic](../../../Logic/model-theory/compactness-theorem-for-first-order-logic.md)

## Sources

- U. Waldmann, *Automated Reasoning II*, lecture notes, Max Planck Institute for Informatics, summer semester 2024, <https://rg1-teaching.mpi-inf.mpg.de/autrea2-ss24/notes-current.pdf>, Section 1.11, Theorem 1.7 with its proof, p. 28.
