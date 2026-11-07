# The run assignment satisfies the situation-definition family

Let $M$ be a finite stack
machine with encoding data $E$, let $N$ be the number of situations of $E$, let $s$ be an input
of $M$, and let $T, H \in \mathbb{N}$ with $d \le H$, where $d$ is the window depth of $M$. Then
the run assignment of $s$ for $T$ and $H$ (true exactly on the run literals) satisfies the
transition clause family of the layout of $E$ at height $H$, for times $t < T$ and situations
$i < N$, with the tables $\mathrm{la}$ and $\mathrm{wa}$ of $E$ and with the situation positions
$\mathrm{sa}$ of $E$ in place of the next-label table.

In the clause of the real situation, the head literal is the real situation literal, by the
definition of the run literals.
