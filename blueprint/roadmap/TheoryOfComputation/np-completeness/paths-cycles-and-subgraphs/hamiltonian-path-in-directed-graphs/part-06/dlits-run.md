# The literals of a clause in the detour walk

Let $y \in \mathbb{N}$ have binary encoding
$\mathrm{bin}(y)$ and let $\nu$ and $\rho$ be lists of symbols. For every list $C$ of literals
with token list $\tau$ (the tokens of its literals in order, without a clause separator), all
bits $p_+, p_-, b$, and every quiescent state $s$ of the emitter such that $F$ holds $\tau$
followed by $\rho$, $V$ holds the name of $y$, then a clause separator, then $\nu$, and the
scratch stack $X$ is empty, there is a state bit $b'$ such that the emitter goes in at most
$|\tau|(3|\mathrm{bin}(y)| + 6)$ steps from the detour-walk label with clause flags
$(p_+, p_-)$, state bit $b$ and the stacks of $s$ to the detour-walk label with clause flags
$(p_+ \lor ((y, \mathrm{true}) \in C), p_- \lor ((y, \mathrm{false}) \in C))$ and state bit $b'$,
with the stacks of $s$ changed as follows: $F$ becomes $\rho$ and $\tau$ reversed is prepended to
$T$.
