# The simulation halts one step after the Post–Turing machine

Let $M$ be a Post–Turing machine over a
finite alphabet $\Gamma_0$ with blank symbol $b$ and at least one non-blank symbol, supported by a
finite set $S$ of states, and let $\widehat{M}$ be the single-tape machine over the non-blank
symbols $N = \Gamma_0 \setminus \{b\}$ simulating $M$. For a tape $t$ over $N$, write $\tau(t)$
for the Post–Turing machine tape read from $t$ cell by cell. If $q \in S$ and $M$ has no step from the
configuration $(q, \tau(t))$, then one step of $\widehat{M}$ from the configuration $(q, t)$
leads to its halting state with the tape $t$ unchanged.
