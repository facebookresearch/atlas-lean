# Completeness of the five clause families

Let $E$ be an encoding of the machine $M$, let
$x$, $y$ and $Y$ be words over the input alphabet such that every letter of $y$ occurs in $Y$, and
let $m$ and $T$ be natural numbers with $|xy| \le m$, where $xy$ is the concatenation. Let $d$ be
the window depth of $M$, let $H = m + (T + 1)d + 1$ be the stack cap, and let $a$ be the
assignment of the real run's literals of $xy$ for $T$ steps at height $H$. Suppose that the
configuration reached after $T$ steps of the idle-extended run of $M$ from the initial
configuration on $xy$ is accepting for the output symbol $\mathrm{acc}$: it is halted, its state
is the initial state of $M$, and $\mathrm{acc}$ is on top of its output stack. Then the length of
$a$ is the number of variables of the transition-clause formula for $T$ and $H$, and $a$
satisfies each of the following, all for $T$ steps at height $H$: the update family (the
transition clause family with tables $\mathrm{la}$, $\mathrm{na}$, $\mathrm{wa}$ and $N$
situations), the S-definition family (the transition clause family with tables $\mathrm{la}$,
$\mathrm{sa}$, $\mathrm{wa}$ and $N$ situations), the cell-shift family with tables
$\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ and $N$ situations, the init family for
$x$, $Y$ and $m$, and the accept family for $\mathrm{acc}$.

No bound $|x| \le m$ and no encodability of $\mathrm{acc}$ is needed in this direction.
