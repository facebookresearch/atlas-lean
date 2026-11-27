# Ambainis–Filmus–Le Gall: limitations of the Coppersmith–Winograd analysis

Consider the laser method applied to tensor powers $\mathrm{CW}_q^{\otimes 2^m}$ in the analysis framework of Coppersmith-Winograd, Stothers, Vassilevska Williams and Le Gall, in which the value of each power is bounded via values of its constituent tensors computed recursively. For $q = 5$ and every $m$, this framework cannot prove $\omega < 2.3725$. Moreover, even with arbitrary constituent values of the stated form (the ``merging'' strategy), no bound below $2.3078$ is attainable for any power of $\mathrm{CW}_5$. For smaller $q$, the merging barrier deteriorates monotonically (giving $2.2387$ for $q = 1$, $2.2540$ for $q = 2$, $2.2725$ for $q = 3$, $2.2907$ for $q = 4$, and $2.3078$ for $q = 5$, with the framework limits computed in Table 1 for $q \le 8$).

## Proof sketch

For a fixed $q$ (in particular $q = 5$), the value bounds obtained in the framework are upper bounded by a convex program expressing the method's estimate of $V_\tau(\mathrm{CW}_q^{\otimes 2^m})$ in terms of entropies of distributions on block triples with constraints coming from the marginals. One shows the program's optimum converges as $m \to \infty$ and evaluates the limit numerically, showing for $q = 5$ that every upper bound on $\omega$ obtainable in the framework is at least $2.3725$; a relaxation in which constituent values are arbitrary gives the merging barrier ($2.3078$ at $q = 5$, and the smaller per-$q$ limits for $q \le 4$).

## Depends on

- [The Coppersmith–Winograd tensor](cw-tensor.md)
- [The value of a tensor in the laser method](tensor-value.md)

## Proof depends on

- [The laser method bound on omega from tensor values](laser-method-bound.md)
- [Le Gall's 2014 bound on the square exponent](../matrix-multiplication-exponent/le-gall2014-upper.md)

## Sources

- A. Ambainis, Y. Filmus, F. Le Gall, "Fast matrix multiplication: limitations of the Coppersmith-Winograd method", STOC (2015), arXiv:1411.5414.
