# Certified rational approximation of cos/sin(2 pi / 2^k) and 1/sqrt 2

This node collects certified rational approximation of the constants needed for exactly unitary gate approximants.

## Expansion

A sound expansion has separate pages for:

1. **Trigonometric values.** For an integer $k \ge 0$ and a rational accuracy $\varepsilon > 0$, rationals within
   $\varepsilon$ of $\cos(2\pi/2^k)$ and $\sin(2\pi/2^k)$, computed in time polynomial in $k$ and $\log(1/\varepsilon)$ with a
   certified error bound (for example from truncated Taylor series with explicit remainder).
2. **Inverse square root of two.** A rational within $\varepsilon$ of $1/\sqrt 2$ with the same kind of bound.
3. The numerical constructions are stated independently of their use in quantum circuits.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Algorithm cost model.

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §2.2 (approximate universality of gate sets; background, not a statement of this numerical construction). <https://arxiv.org/pdf/1907.09415v6>
