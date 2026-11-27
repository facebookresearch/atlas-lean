# Long code and folded tables

Let $\alpha$ be a finite set. The *long code* of $a \in \alpha$ is the table $\mathrm{LC}(a) : \{0,1\}^\alpha \to \{0,1\}$, $\mathrm{LC}(a)(g) = g(a)$, i.e. the dictator function on the $|\alpha|$-dimensional cube indexed by $a$; equivalently it is the Hadamard encoding of the unit vector $e_a \in \mathbb{F}_2^\alpha$. A table $B : \{0,1\}^\alpha \to \{0,1\}$ is *folded* (odd) if $B(\bar g) = \overline{B(g)}$ for every $g$, where $\bar g$ is the complement. In $\pm 1$ notation the Fourier expansion of a folded table is supported on sets of odd size, and long codes are folded. Distinct long codes are at relative distance exactly $1/2$.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Fourier character on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/cube-chi.md)
- [Local decoding of the Hadamard code](../../../InformationTheory/error-correcting-codes/hadamard-code-local-decoding.md)

## Sources

- J. Håstad, "Some Optimal Inapproximability Results", Journal of the ACM 48(4), 2001.
- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
