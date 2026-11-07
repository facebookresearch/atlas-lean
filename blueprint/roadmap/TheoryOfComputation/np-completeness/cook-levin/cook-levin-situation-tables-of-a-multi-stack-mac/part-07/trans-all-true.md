# The all-true assignment satisfies the transition, shift and init families

Let $E$ be an
encoding of a machine $M$ with window depth $d$, let $x$ and $Y$ be lists of symbols of the input
stack of $M$, and let $m, T, H \in \mathbb{N}$ with $|x| \le m < H$ and $d \le H$. Write
$\mathrm{la}, \mathrm{na}, \mathrm{sa}, \mathrm{wa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu}$ for the
situation tables of $E$, $N$ for its number of situations and $V$ for the number of variables of
its layout at bounds $T$ and $H$. Then the all-true assignment of length $V$ satisfies each of the
following families at bounds $T$ and $H$: the transition clause family of the layout of $E$ for
$N$ situations with tables $\mathrm{la}$, $\mathrm{na}$, $\mathrm{wa}$ (the update family); the
transition clause family for $N$ situations with tables $\mathrm{la}$, $\mathrm{sa}$,
$\mathrm{wa}$ (the S-definition family); the cell-shift clause family for $N$ situations with
tables $\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$; and the init family of $E$ for
$x$, $Y$, $m$.

Every clause of these families has a positive literal at an index below $V$.
