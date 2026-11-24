# Circuits that compute the matrix product

A circuit $c$ over a field $F$ whose inputs are
the entries of an $m \times r$ matrix and an $r \times n$ matrix computes matrix multiplication
when, for all matrices $A \in F^{m \times r}$ and $B \in F^{r \times n}$ and all $i < m$, $j < n$,
its output at $(i, j)$ on the entries of $A$ and $B$ equals $(AB)_{ij}$.

Correctness is required on actual values in $F$, not as an identity of formal polynomials.
