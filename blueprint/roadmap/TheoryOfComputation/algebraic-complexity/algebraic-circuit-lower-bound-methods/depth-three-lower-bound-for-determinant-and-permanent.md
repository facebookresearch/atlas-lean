# Depth-three circuits of bounded product fan-in for the determinant and permanent

A depth-three ($\Sigma\Pi\Sigma$) circuit with product fan-in at most $d$ computes $\sum_{i=1}^s\prod_{j=1}^{d}\ell_{ij}$ with affine forms $\ell_{ij}$. If such a circuit computes $\det_n$ or $\mathrm{per}_n$, then for every $k$, $s\binom dk\ge\binom nk^2$; in particular, if $d\le n$ then (taking $k=\lfloor n/2\rfloor$) $s\ge\binom{n}{\lfloor n/2\rfloor}=2^{\Omega(n)}$.

## Proof sketch

Subadditivity of $\mu_k$ and the bound $\binom dk$ for each product, compared with the lower bound $\binom nk^2$ for the determinant and permanent.

## Depends on

- [The partial-derivative measure](partial-derivative-measure.md)

## Proof depends on

- [Partial derivatives of the generic determinant and permanent](partial-derivatives-of-determinant-and-permanent.md)

## Sources

- Noam Nisan, Avi Wigderson, "Lower Bounds on Arithmetic Circuits via Partial Derivatives", Computational Complexity, 1996.
- Neeraj Kayal, Ramprasad Saptharishi, "A Selection of Lower Bounds for Arithmetic Circuits", Perspectives in Computational Complexity: The Somenath Biswas Anniversary Volume, 2014.
