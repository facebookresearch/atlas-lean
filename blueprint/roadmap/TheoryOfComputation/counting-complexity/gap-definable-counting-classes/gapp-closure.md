# Closure properties of GapP

$\mathsf{GapP}$ is closed under negation, addition, multiplication, and under sums $\sum_{|y|\le p(|x|)}f(x,y)$ and products $\prod_{i\le p(|x|)}f(x,i)$ of polynomially many terms, and under binomial coefficients $\binom{f(x)}{k}$ for constant $k$. Every polynomial-time computable integer-valued function is in $\mathsf{GapP}$, and $\mathsf{GapP}\subseteq\mathsf{FP}^{\#\mathsf{P}}$.

## Proof sketch

Combine machines: for sums branch over $y$; for products run the machines in sequence and multiply signs; differences of counts handle negation. Binomial coefficients choose $k$ distinct accepting paths in increasing order, which handles $\#\mathsf{P}$ functions; for a gap $f=\#\mathrm{acc}-\#\mathrm{rej}$ one expands $\binom{f}{k}$ by a Vandermonde-type identity into binomials of path counts.

## Depends on

- [GapP and the gap-definable classes SPP, WPP, LWPP, AWPP, C=P and Mod_kP](gap-definable-classes.md)

## Sources

- Stephen A. Fenner, Lance J. Fortnow and Stuart A. Kurtz, "Gap-Definable Counting Classes", Journal of Computer and System Sciences 48(1), 1994, Proposition 3.5, Closure Properties 1–5 and Lemma 3.7.
- Lance Fortnow, "Counting Complexity", Complexity Theory Retrospective II, 1997.
