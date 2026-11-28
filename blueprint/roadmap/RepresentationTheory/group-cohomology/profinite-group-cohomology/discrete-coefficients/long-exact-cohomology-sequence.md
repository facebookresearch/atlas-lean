# The long exact cohomology sequence

Let $G$ be a profinite group and $0 \to A \xrightarrow{i} B \xrightarrow{j} C \to 0$ an exact sequence of discrete
$G$-modules. For a cocycle $c \in Z^n(G, C)$ choose a cochain $b \in C^n(G, B)$ with $j b = c$; then
$\partial b = i a$ for a unique cocycle $a \in Z^{n+1}(G, A)$, and $\delta[c] = [a]$ is a well-defined homomorphism,
the connecting homomorphism

$$
\delta \colon H^n(G, C) \longrightarrow H^{n+1}(G, A)
$$

of [cohomology](cohomology-with-discrete-coefficients.md). The sequence

$$
0 \to A^G \to B^G \to C^G \xrightarrow{\delta} H^1(G, A) \to \cdots \to H^n(G, A) \to H^n(G, B) \to H^n(G, C)
\xrightarrow{\delta} H^{n+1}(G, A) \to \cdots
$$

is exact.

For abstract groups, with coefficients in representations, Mathlib has the connecting homomorphism
`groupCohomology.δ` and the exactness `groupCohomology.mapShortComplex₁_exact` (and its companions for the other
two spots); the statement here is the one for profinite groups and continuous cochains.

## Depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  the cochains, cocycles and cohomology groups

## Proof depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  the exact sequence of cochain complexes $0 \to C^\bullet(G, A) \to C^\bullet(G, B) \to C^\bullet(G, C) \to 0$, to
  which the snake lemma applies

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §3, Theorem (1.3.2) and its
  proof, p. 27, and the description of $\delta$ in the proof of (1.3.3), p. 28.
