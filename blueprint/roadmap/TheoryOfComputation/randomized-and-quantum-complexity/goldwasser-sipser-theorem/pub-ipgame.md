# Public-coin interactive-proof game

The game takes a length cap $c$, a number $k$ of
fresh coins per round, a verifier message function $V_{\mathrm{msg}}$, a verifier decision
function $V_{\mathrm{dec}}$, a prover $P$ mapping pairs of a coin prefix and a transcript (a list
of bitstrings) to bitstrings, an input $x$, a coin string $\rho$, a number $j$ of remaining
rounds, a total number $T$ of rounds and a transcript $t$, and returns a Boolean outcome. If
$j = 0$, the outcome is $V_{\mathrm{dec}}(x, \rho, t)$. Otherwise let $\pi$ be the first
$(T - j + 1) k$ coins of $\rho$ (all of $\rho$ if it is shorter), where $T - j$ is truncated
subtraction ($0$ when $j > T$). The verifier sends $m = V_{\mathrm{msg}}(x, \pi, t)$ and the
prover replies $a = P(\pi, t')$, where $t'$ is $t$ extended by $m$. If both $m$ and $a$ have
length at most $c$, the outcome is that of the game with $j - 1$ remaining rounds, the same
$T$, and transcript $t$ extended by $m$ and then $a$; otherwise the outcome is false.

So the verifier's message and the prover's reply in a round see only the coins revealed up to
that round, while the final decision may use the whole coin string.
