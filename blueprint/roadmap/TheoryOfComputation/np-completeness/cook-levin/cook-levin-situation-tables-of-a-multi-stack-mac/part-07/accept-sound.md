# Satisfying assignments yield accepting runs

Let $E$ be an encoding of a finite stack
machine $M$ with input stack $k_0$ and output stack $k_1$, let $x$ and $Y$ be lists of symbols of
$k_0$, let $m, T \in \mathbb{N}$ with $|x| \le m$, and let $\alpha$ be a symbol of $k_1$ that is one
of the effective symbols of $E$ for $k_1$. Put $H = m + (T + 1)d + 1$, where $d$ is the window
depth of $M$, and let $N$ be the number of situations of $E$. Suppose an assignment $a$ satisfies,
at bounds $T$ and $H$, the update family (the transition clause family of the layout of $E$ with
tables $\mathrm{la}, \mathrm{na}, \mathrm{wa}$ and $N$ situations), the S-definition family (the
same with $\mathrm{sa}$ in place of $\mathrm{na}$), the cell-shift family with tables
$\mathrm{sa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu}$ and $N$ situations, the init family for $x$,
$Y$ and $m$, and the accept family for $\alpha$. Then there is a list $y$ whose entries all occur
in $Y$ such that $|xy| \le m$ and the idle-extended run of $M$ from the initial configuration on
input $xy$ is, after $T$ steps, an accepting configuration for $\alpha$.

Apart from the accept family, no one-hot or at-most-one clauses are assumed.
