# The full program

Let $\gamma : \mathrm{Fin}\,r \to \mathrm{Fin}\,g$ code the raw
symbols, let $\sigma \in \mathrm{Fin}\,g$ be a separator code, let $k$ be a polynomial with
natural-number coefficients, let $c, e, d \in \mathbb{N}$, and let $h$ be a host program with
labels $\Lambda$ and start label $\lambda_0 \in \Lambda$. The full program, whose counter-program
labels have $D$ Horner rounds for $D$ the length of the coefficient list of $k$, runs at the
read-loop label the read loop for $\gamma$ and $\sigma$ over all raw symbols; at a
counter-program label $l$ other than the final one, the counter program for $k, c, e, d$ at $l$,
embedded with its scratch counters on the full machine's private counters, its target counters on
the corresponding host counters and its output on the host output; at the final counter-program
label, a step that sets the state to false and jumps to the host label $\lambda_0$; and at a host
label $l$, the statement $h(l)$ on the host stacks.
