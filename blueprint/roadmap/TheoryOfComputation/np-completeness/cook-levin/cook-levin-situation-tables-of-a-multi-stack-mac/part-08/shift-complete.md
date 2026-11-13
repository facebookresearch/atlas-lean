# The run assignment satisfies the cell-shift family

Let $M$ be a finite stack machine
with encoding data $E$, let $N$ be the number of situations of $E$, let $s$ be an input of $M$,
and let $T, H \in \mathbb{N}$ with $d \le H$, where $d$ is the window depth of $M$. For
$t \in \mathbb{N}$ let $c_t$ be the configuration after $t$ steps of the idle-extended run of $M$
from its start configuration on $s$, and suppose that for every $t < T$ every stack of $c_t$ has
length at most $H - d$. Then the run assignment of $s$ for $T$ and $H$ (true exactly on the run
literals) satisfies the cell-shift clause family (shift, overflow and pushed-fill clauses) of the
layout of $E$ with the tables $\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ of $E$,
for $N$ situations, times $t < T$ and height $H$.

Off the real situation the negated situation literal is true; on it, the target cell of row
$t + 1$ is the one given by the table-driven row update.
