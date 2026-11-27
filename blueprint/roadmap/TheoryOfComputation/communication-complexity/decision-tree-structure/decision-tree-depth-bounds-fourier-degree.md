# Functions computed by depth-d trees have Fourier degree at most d and total influence at most d

Let $T$ be a decision tree of depth $d$ over $\{0,1\}^n$ with leaves labelled in a set $\beta$, and $g : \beta \to \mathbb{R}$. Then $x \mapsto g(T(x))$ has Fourier coefficients vanishing on all sets of size greater than $d$. In particular a Boolean function of decision tree complexity $d$, read as $\pm 1$, has total influence at most $d$, and total influence equals average sensitivity, so $\mathrm{I}[f] = \mathbb{E}_x[s(f, x)] \le s(f)$.

## Proof sketch

Each consistent root-to-leaf path contributes $g(\text{label})$ times the indicator of the subcube it fixes, of codimension at most $d$ (these subcubes partition the cube), a product of at most $d$ affine functions of single coordinates. Total influence is $\sum_S |S|\hat f(S)^2 \le d \sum_S \hat f(S)^2 = d$.

## Depends on

- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)

## Proof depends on

- [Total influence in Fourier form](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence-eq-sum-card-mul-sq.md)
- [Total influence is at most the degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/spectral-structure-of-boolean-functions/bool-total-influence-le-degree.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
