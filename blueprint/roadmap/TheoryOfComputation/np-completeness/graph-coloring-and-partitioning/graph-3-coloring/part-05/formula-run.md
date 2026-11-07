# The emitter on a list of clauses

Let $L_b$ be a natural number, $o_0$ a list of bits,
$C_s$ a list of clauses, $s$ a construction state and $\tau$ a natural number, and let $T$ be the
concatenation over the clauses $C$ of $C_s$, in order, of the tokens of $C$ as they lie on the
token stack. If the size invariant holds for $\tau$ and $s$ and $\tau + |T| \le L_b$, then for
every local state $v$ the emitter goes from label cls with the quiescent state of $s$ with
tokens $T$, output above $o_0$, OR output $0$ and first-literal flag $0$, to label cls again,
with some local state, in at most $|T| \cdot (400 (L_b + 1)^2 + 1)$ steps. It ends in the
quiescent state of $s'$ with no tokens, output above $o_0$, OR output $0$ and first-literal
flag $0$, where $s'$ is obtained from $s$ by applying the one-clause step of the 3-coloring
construction to the clauses of $C_s$ in order.
