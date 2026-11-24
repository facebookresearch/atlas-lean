# Init obligation, input pinned

Let $E$ be an encoding of a machine $M$ with window depth
$d$, let $a$ be an assignment, let $x$ and $Y$ be lists of symbols of the input stack of $M$, and
let $m, T$ be natural numbers, and put $H = m + (T + 1)d + 1$. The init obligation for $a$, $x$,
$Y$, $m$ and $T$ holds when there is a list $y$ of symbols of $Y$ with $|x| + |y| \le m$ such that
the row-0 obligation holds for $a$ at height $H$ and the input $x$ followed by $y$: under $a$, the
code literal of row $0$ and the cell literals of row $0$ at every depth below $H$ are true for the
initial configuration of $M$ on that input.
