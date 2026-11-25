# Snapping approximate values to exact Gaussian-rational unitaries

This node collects the computation of exactly unitary Gaussian-rational matrices from approximate numerical data.

The geometric core is the following stereographic snapping guarantee. A rational approximation $w$ of a unit vector in $\mathbb{R}^2$ or $\mathbb{R}^4$ is projected
stereographically from the pole opposite in sign to a largest-magnitude coordinate of $w$, and the projection is inverted exactly
over $\mathbb{Q}$. The result is an exact rational point of $S^1$ or $S^3$; an exact rational point of the sphere is returned unchanged;
and if every coordinate of $w$ is within $\delta$ of the target, the snapped point is within distance $3\delta$ of it on $S^1$ when
$\delta \le 1/4$, and within $4\delta$ on $S^3$ when $\delta \le 1/8$.

## Expansion

A sound expansion adds pages for the parts that are not yet stated:

1. **Bit length.** For input coordinates of $O(\log(1/\varepsilon))$ bits, the snapped coordinates have $O(\log(1/\varepsilon))$ bits.
2. **Running time.** Snapping and the construction below run in time polynomial in the input bit length.
3. **Unitary encoding.** The map from a rational point of $S^1$ or $S^3$ to an exactly unitary matrix with entries in $\mathbb{Q}(i)$
   that parametrizes the target gate, and the transfer of the distance bound to an $O(\varepsilon)$ bound in operator norm.
   Density of rational unitaries alone does not give such a procedure.

## Proof depends on

- [Exactly unitary Gaussian-rational approximations of 1- and 2-qubit gates](exactly-unitary-gaussian-rational-approximations-of-1-and-2.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §2.2 (approximate universality of gate sets; background, not a statement of this procedure). <https://arxiv.org/pdf/1907.09415v6>
