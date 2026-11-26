# Classical soundness of the low individual degree test

There is a function $\delta(m, d, \varepsilon, |\mathbb{F}|)$, polynomial in $m$, $d/|\mathbb{F}|$ and a fixed root of $\varepsilon$, such that if deterministic classical players pass the low individual degree test with probability at least $1 - \varepsilon$, then there is a polynomial $g$ of individual degree at most $d$ agreeing with the point player's answers on all but a $\delta$ fraction of $\mathbb{F}^m$.

## Proof sketch

Induct on $m$: restrict to slices with the last coordinate fixed, apply the induction hypothesis on most slices, and paste the slice polynomials by interpolation along axis-parallel lines in the last coordinate, using the Schwartz–Zippel bound $d/|\mathbb{F}|$ to control disagreement.

## Depends on

- [The low individual degree test](the-low-individual-degree-test.md)

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "Quantum Soundness of the Classical Low Individual Degree Test", arXiv:2009.12982, 2020.
