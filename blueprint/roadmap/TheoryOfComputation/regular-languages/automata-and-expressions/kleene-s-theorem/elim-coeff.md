# Coefficient after eliminating the last state

Let $\alpha$ be an alphabet, $n \in \mathbb{N}$, and let $A = (A_{ij})_{0 \le i, j \le n}$ be languages over $\alpha$.
Eliminating the last index $n$ gives the coefficients $(A'_{ij})_{0 \le i, j < n}$ defined by

$$A'_{ij} = A_{ij} \cup A_{in}\, A_{nn}^*\, A_{nj},$$

the old coefficient together with the detour through $n$, which may loop at $n$ any number of times.
