# Khot–Vishnoi integrality gaps for unique games and cut problems

For every $\varepsilon > 0$ and $\eta > 0$ there are unique-games instances whose standard SDP relaxation (with triangle inequalities) has value at least $1 - \eta$ while their optimum is at most $\varepsilon$, with label size $R = 2^{\Theta(\log(1/\varepsilon)/\eta)}$. As a consequence, negative-type metrics do not embed into $\ell_1$ with constant distortion: there are $n$-point negative-type metrics requiring distortion $\Omega\bigl((\log \log n)^{c}\bigr)$ for some constant $c > 0$, and the Goemans-Linial SDP for sparsest cut has an unbounded integrality gap.

## Proof sketch

The instance lives on the Boolean cube modulo the Hadamard code: vertices are cosets of the code, labels are elements of the coset, and constraints come from noisy hypercube edges. The SDP solution uses tensored characters, satisfying triangle inequalities; soundness follows from the KKL-type statement that low-influence Boolean functions are noise sensitive, so no labelling satisfies many constraints. Composing the gap instance with the long-code reduction yields the metric non-embeddability.

## Depends on

- [The integrality gap curve of the basic SDP](integrality-gap-curve.md)
- [The Unique Games Conjecture](../pcp-constructions/the-unique-games-conjecture.md)

## Proof depends on

- [KKL inequality for $p$-biased measures](../../../Combinatorics/boolean-functions/kahn-kalai-linial-inequality/kkl-pbiased.md)

## Sources

- S. Khot, N. K. Vishnoi, "The Unique Games Conjecture, integrality gap for cut problems and embeddability of negative-type metrics into $\ell_1$", Journal of the ACM 62(1) (2015), FOCS (2005).
