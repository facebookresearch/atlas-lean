# The run assignment satisfies the update family

Let $M$ be a finite stack machine with
encoding data $E$, let $N$ be the number of situations of $E$, let $s$ be an input of $M$, and
let $T, H \in \mathbb{N}$ with $d \le H$, where $d$ is the window depth of $M$. For
$t \in \mathbb{N}$ let $c_t$ be the configuration after $t$ steps of the idle-extended run of $M$
from its start configuration on $s$, and suppose that for every $t < T$ every stack of $c_t$ has
length at most $H - d$. Then the run assignment of $s$ for $T$ and $H$ (true exactly on the run
literals) satisfies the transition clause family of the layout of $E$ at height $H$, for times
$t < T$ and situations $i < N$, with the tables $\mathrm{la}$, $\mathrm{na}$ and $\mathrm{wa}$
of $E$.

In the clause of the real situation, the head literal is the code of the real next
configuration, by the agreement of the tables with the machine's step.
