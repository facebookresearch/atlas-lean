# PCP over a finite alphabet many-one reduces to PCP over the binary alphabet

Let $\alpha$
be a finite alphabet with a primitive recursive encoding of its letters as natural numbers. Then
the Post correspondence problem over $\alpha$ is many-one reducible to the Post correspondence
problem over the two-letter alphabet of Booleans $\mathrm{true}$ and $\mathrm{false}$: there is a
computable map $f$ sending each finite list $P$ of dominoes over $\alpha$ to a finite list $f(P)$
of dominoes over the Booleans such that $P$ has a PCP solution if and only if $f(P)$ has a PCP
solution.
