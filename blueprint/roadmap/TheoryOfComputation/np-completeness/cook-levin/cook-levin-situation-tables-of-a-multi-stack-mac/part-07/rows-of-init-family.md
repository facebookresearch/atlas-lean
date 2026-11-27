# A satisfying assignment tracks a certified run

Let $E$ be an encoding of a machine $M$
with window depth $d$, let $x$ and $Y$ be lists of symbols of the input stack of $M$, let
$m, T \in \mathbb{N}$ with $|x| \le m$, and let $H = m + (T + 1)d + 1$ be the corrected stack cap.
Write $\mathrm{la}, \mathrm{na}, \mathrm{sa}, \mathrm{wa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu}$
for the situation tables of $E$ and $N$ for its number of situations. Suppose an assignment $a$
satisfies the following families at bounds $T$ and $H$: the transition clause family of the layout
of $E$ for $N$ situations with tables $\mathrm{la}$, $\mathrm{na}$, $\mathrm{wa}$ (the update
family); the transition clause family for $N$ situations with tables $\mathrm{la}$,
$\mathrm{sa}$, $\mathrm{wa}$ (the S-definition family); the cell-shift clause family for $N$
situations with tables $\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$; and the init
family of $E$ for $x$, $Y$, $m$. Then there is a list $y$ of symbols, each in $Y$, with
$|xy| \le m$ such that for every $t \le T$, if $c_t$ is the configuration after $t$ steps of the
idle-extended run of $M$ from the initial configuration on input $xy$, then under $a$ the variable
of row $t$ for the (label, state) code of $c_t$ is true, and for every stack number $k$ of $E$ and
every depth $j < H$ the variable of row $t$ for stack $k$, depth $j$ and the cell code of $c_t$ at
$(k, j)$ is true.
