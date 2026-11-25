# One literal of the detour walk

Let $y \in \mathbb{N}$ have binary encoding
$\mathrm{bin}(y)$, let $l = (z, b)$ be a literal with token list $\tau$, let $\rho$ and $\nu$ be
lists of symbols, let $p_+$, $p_-$ and $v$ be bits, and let $s$ be a quiescent state of the
HAMPATH emitter such that $F$ holds $\tau$ followed by $\rho$, $V$ holds the name of $y$, then
the clause symbol $\mathrm{cl}$, then $\nu$, and the scratch stack $X$ is empty. Then there is a
bit $v'$ such that the emitter goes in at most $3|\mathrm{bin}(y)| + |\tau| + 5$ steps from the
detour-walk label with clause flags $(p_+, p_-)$, state bit $v$ and the stacks of $s$ to the
detour-walk label with clause flags $(p_+ \lor (z = y \land b), p_- \lor (z = y \land \lnot b))$
and state bit $v'$, with the stacks of $s$ changed as follows: $F$ becomes $\rho$ and $\tau$
reversed is prepended to $T$.
