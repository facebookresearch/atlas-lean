# Each TM0 step is one step of the simulation

Let $M$ be a TM0 machine over a finite
alphabet $\Gamma_0$ with blank symbol $b$ and at least one non-blank symbol, supported by a finite
set $S$ of states, and let $\widehat{M}$ be the single-tape machine over the non-blank symbols
$N = \Gamma_0 \setminus \{b\}$ simulating $M$. For a tape $t$ over $N$, write $\tau(t)$ for the
TM0 tape read from $t$ cell by cell. If $q \in S$ and one step of $M$ takes the configuration
$(q, \tau(t))$ to a configuration $(q', T')$, then $q' \in S$ and there is a tape $t'$ over $N$
with $\tau(t') = T'$ such that one step of $\widehat{M}$ takes the configuration $(q, t)$ to the
configuration $(q', t')$.
