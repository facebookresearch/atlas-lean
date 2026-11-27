# Depth-three circuits of bounded product fan-in for the determinant and permanent

A depth-three ($\Sigma\Pi\Sigma$) circuit with product fan-in at most $d$ computes $\sum_{i=1}^s\prod_{j=1}^{d}\ell_{ij}$ with affine forms $\ell_{ij}$. Over every field, if such a circuit computes $\det_n$ or $\mathrm{per}_n$ (which forces $d\ge n$, as these have degree $n$), then $s\binom dk\ge\binom nk^2$ for every $0\le k\le n$; in particular, if $d=n$ then (taking $k=\lfloor n/2\rfloor$) $s\ge\binom{n}{\lfloor n/2\rfloor}=2^{\Omega(n)}$.

## Proof sketch

Subadditivity of $\mu_k$ and the bound $\binom dk$ for each product, compared with the lower bound $\binom nk^2$ for the determinant and permanent.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Proof depends on

- [The partial-derivative measure](partial-derivative-measure.md)
- [Partial derivatives of the generic determinant and permanent](partial-derivatives-of-determinant-and-permanent.md)

## Sources

- Noam Nisan, Avi Wigderson, "Lower Bounds on Arithmetic Circuits via Partial Derivatives", Computational Complexity, 1996.
- Neeraj Kayal, Ramprasad Saptharishi, "A Selection of Lower Bounds for Arithmetic Circuits", Perspectives in Computational Complexity: The Somenath Biswas Anniversary Volume, 2014.
