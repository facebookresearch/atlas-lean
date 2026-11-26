# Ambainis–Filmus–Le Gall: limitations of the Coppersmith–Winograd analysis

Consider the laser method applied to tensor powers $\mathrm{CW}_q^{\otimes 2^m}$ in the analysis framework of Coppersmith-Winograd, Stothers, Vassilevska Williams and Le Gall, in which the value of each power is bounded via values of its constituent tensors computed recursively. For every $q$ and every $m$, this framework cannot prove $\omega < 2.3725$. Moreover, even with arbitrary constituent values of the stated form (the ``merging'' strategy), no bound below $2.3078$ is attainable for any power of any $\mathrm{CW}_q$.

## Proof sketch

The value bounds obtained in the framework are upper bounded by a convex program expressing the method's estimate of $V_\tau(\mathrm{CW}_q^{\otimes 2^m})$ in terms of entropies of distributions on block triples with constraints coming from the marginals. One shows the program's optimum converges as $m \to \infty$ and evaluates the limit, which shows that every upper bound on $\omega$ obtainable in the framework is at least $2.3725$; a relaxation in which constituents are arbitrary gives the weaker universal bound.

## Depends on

- [The Coppersmith–Winograd tensor](cw-tensor.md)
- [The value of a tensor in the laser method](tensor-value.md)

## Proof depends on

- [The laser method bound on omega from tensor values](laser-method-bound.md)
- [Le Gall's 2014 bound on the square exponent](../matrix-multiplication-exponent/le-gall2014-upper.md)

## Sources

- A. Ambainis, Y. Filmus, F. Le Gall, "Fast matrix multiplication: limitations of the Coppersmith-Winograd method", STOC (2015), arXiv:1411.5414.
