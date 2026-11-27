# Wang bars and the tiling problem for k Wang bars

A Wang bar is a horizontal strip of unit squares whose unit edges carry colors; the tiling problem for $k$ Wang bars asks
whether a given set of $k$ bars tiles the plane by translation with matching colors.

A *Wang bar of length $\ell$*, for an integer $\ell \ge 1$, is an $\ell \times 1$ rectangle, horizontal side of length $\ell$,
divided into $\ell$ unit squares, in which each of the $\ell$ unit segments of its top side, each of the $\ell$ unit segments of
its bottom side, and each of its two vertical sides carries a color. A [Wang tile](wang-tiles-and-valid-tilings.md) is a Wang bar
of length $1$. A set $B$ of Wang bars *tiles the plane* if the plane can be covered without overlap by translated copies of bars
of $B$, placed on the integer grid without rotation or reflection, so that any two unit segments shared by adjacent bars carry the
same color.

For a fixed positive integer $k$, the *tiling problem for $k$ Wang bars* is the decision problem: given a set of $k$ Wang bars,
does it tile the plane? The number $k$ of bars is fixed; their lengths and colors are part of the input, so the problem has
infinitely many instances, unlike the tiling problem for a fixed number of Wang tiles.

For a finite set $T$ of Wang tiles, let $n(T) = |T|$ and let $c(T)$ be the maximum, over the four sides, of the number of
different colors that the tiles of $T$ carry on that side. The *color deficiency* of $T$ is $cd(T) = n(T) - c(T) \ge 0$.

## Depends on

- [Wang tiles and valid tilings](wang-tiles-and-valid-tilings.md)

## Proof depends on

None.

## Sources

- C. Yang and Z. Zhang, "Undecidability of tiling the plane with a fixed number of Wang bars", *Journal of the Operations Research Society of China*, published online 2026, doi:10.1007/s40305-025-00666-0; numbering of the version arXiv:2404.04504v1: Definitions 2 (color deficiency) and 3 (tiling problem for $k$ Wang bars) and the description of Wang bars before Definition 3.
- E. Jeandel and N. Rolin, "Fixed parameter undecidability for Wang tilesets", in *AUTOMATA and JAC 2012*, Electronic Proceedings in Theoretical Computer Science 90, pp. 69–85, 2012, doi:10.4204/EPTCS.90.6 (Wang bars and the parameter $n - c$).
