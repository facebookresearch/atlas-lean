# The full program on the real generators

For an encoding $E$ of a machine $M$, a list
$Y$ of symbols of the input stack alphabet of $M$, a symbol $a$ of the output stack alphabet of
$M$, a map $\iota$ from the raw symbols $\mathrm{Fin}\,r$ to input stack symbols of $M$, an input
stack symbol $\sigma$ of $M$ (the separator), a polynomial $k$ with natural-number coefficients
and $c, e \in \mathbb{N}$, this is the full program in which each raw symbol $i$ is coded by the
code of $\iota(i)$ under $E$, the separator code is the code of $\sigma$ under $E$,
$d = \operatorname{depth} M$, the host program is the host running the real generators of $M$
for $Y$ and $a$, and the host starts at the start label of its initial-row generator.
