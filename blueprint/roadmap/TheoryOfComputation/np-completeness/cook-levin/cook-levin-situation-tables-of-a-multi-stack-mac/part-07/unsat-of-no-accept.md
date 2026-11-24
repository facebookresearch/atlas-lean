# No accepting certificate, no satisfying assignment

Let $E$ be an encoding of a machine
$M$ with window depth $d$, let $x$ and $Y$ be lists of symbols of the input stack of $M$, let
$m, T \in \mathbb{N}$ with $|x| \le m$, let $H = m + (T + 1)d + 1$, and let $\alpha$ be a symbol
of the output stack of $M$ in the effective alphabet of $E$. Write
$\mathrm{la}, \mathrm{na}, \mathrm{sa}, \mathrm{wa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu}$ for
the situation tables of $E$ and $N$ for its number of situations. Suppose that for no list $y$
of symbols, each in $Y$, with $|xy| \le m$, the configuration after $T$ steps of the
idle-extended run of $M$ from the initial configuration on input $xy$ is an accepting
configuration for $\alpha$. Then no assignment satisfies all five of the following families at
bounds $T$ and $H$: the transition clause family of the layout of $E$ for $N$ situations with
tables $\mathrm{la}$, $\mathrm{na}$, $\mathrm{wa}$ (the update family); the transition clause
family for $N$ situations with tables $\mathrm{la}$, $\mathrm{sa}$, $\mathrm{wa}$ (the
S-definition family); the cell-shift clause family for $N$ situations with tables $\mathrm{sa}$,
$\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$; the init family of $E$ for $x$, $Y$, $m$; and the
accept family of $E$ for $\alpha$.

In particular, the all-true assignment does not satisfy all five.
