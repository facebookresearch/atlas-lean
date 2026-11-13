# The five Cook–Levin clause families are satisfiable iff some certificate is accepted

Let $E$ be an encoding of the multi-stack machine $M$, with input stack $k_0$, output stack
$k_1$ and window depth $d$. Let $x$ and $Y$ be lists of input symbols, let $m, T \in \mathbb{N}$,
let $\mathrm{acc}$ be an output symbol, and let $H = m + (T + 1)d + 1$ be the stack cap. Suppose
$|x| \le m$ and $\mathrm{acc}$ is one of the effective symbols that $E$ fixes for stack $k_1$.
Then some list $a$ of Booleans satisfies all five of the following CNF formulas, each for $T$
steps and cap $H$: the transition family with tables $\mathrm{la}, \mathrm{na}, \mathrm{wa}$ and
the transition family with tables $\mathrm{la}, \mathrm{sa}, \mathrm{wa}$, both over the layout
of $E$ and its $N$ situations; the cell-shift family over the same layout with tables
$\mathrm{sa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu}$ and $N$ situations; the init family for $x$,
$Y$ and $m$; and the accept family for $\mathrm{acc}$, if and only if there is a list $y$ of
input symbols, all in $Y$, with $|xy| \le m$ such that the idle-extended run of $M$ from the
initial configuration on input $xy$ is, after $T$ steps, an accepting configuration for
$\mathrm{acc}$: halted, in the initial state, with $\mathrm{acc}$ on top of stack $k_1$.
