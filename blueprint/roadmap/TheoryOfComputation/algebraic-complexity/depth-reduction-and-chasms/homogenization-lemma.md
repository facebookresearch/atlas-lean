# Homogenization and division elimination for arithmetic circuits

If a polynomial $f \in \mathbb{F}[x_1, \dots, x_n]$ of degree $d$ is computed by an arithmetic circuit of size $s$ (possibly with division gates, over an infinite field), then each homogeneous component $f^{[j]}$, $j \le d$, is computed by a single homogeneous division-free circuit of size $O(s d^{2})$ whose gates compute homogeneous polynomials of degree at most $d$.

## Proof sketch

Replace each gate $g$ by $d + 1$ gates computing its homogeneous components $g^{[0]}, \dots, g^{[d]}$; an addition gate adds components degree by degree, and a multiplication gate computes $(gh)^{[j]} = \sum_{i \le j} g^{[i]}h^{[j-i]}$ with $O(d)$ operations. Divisions are eliminated by Strassen's method: after shifting so that the denominator has nonzero constant term, expand the inverse as a truncated geometric series up to degree $d$.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Proof depends on

- [Homogeneous depth-four circuits with bounded bottom fan-in](homogeneous-depth-four.md)

## Sources

- V. Strassen, "Vermeidung von Divisionen", Journal für die reine und angewandte Mathematik 264 (1973) 184-202.
- A. Shpilka, A. Yehudayoff, "Arithmetic circuits: a survey of recent results and open questions", Foundations and Trends in Theoretical Computer Science 5 (2010).
