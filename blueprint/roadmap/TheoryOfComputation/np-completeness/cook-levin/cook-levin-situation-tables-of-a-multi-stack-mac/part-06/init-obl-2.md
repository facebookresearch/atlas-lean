# The init family discharges the init obligation

Let $E$ be an encoding of a machine $M$
with window depth $d$, let $x$ and $Y$ be lists of symbols of the input stack of $M$, and let
$m, T$ be natural numbers with $|x| \le m$, and put $H = m + (T + 1)d + 1$. If an assignment $a$
satisfies the init family of $E$ for $x$, $Y$, $m$, $T$ and $H$, then the init obligation holds
for $a$, $x$, $Y$, $m$ and $T$: there is a list $y$ of symbols of $Y$ with $|x| + |y| \le m$ such
that the row-0 obligation holds for $a$ at height $H$ and the input $x$ followed by $y$.
