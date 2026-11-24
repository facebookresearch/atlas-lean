# Interactive-proof game

The game takes a length cap $c$, a verifier message function
$V_{\mathrm{msg}}$, a verifier decision function $V_{\mathrm{dec}}$, a prover $P$ mapping
transcripts (lists of bitstrings) to bitstrings, an input $x$, a coin string $\rho$, a number
$k$ of rounds and a transcript $t$, and returns a Boolean outcome. If $k = 0$, the outcome is
$V_{\mathrm{dec}}(x, \rho, t)$. Otherwise the verifier sends $m = V_{\mathrm{msg}}(x, \rho, t)$,
and the prover replies $a = P(t')$, where $t'$ is $t$ extended by $m$. If both $m$ and $a$ have
length at most $c$, the outcome is that of the game with $k - 1$ rounds and transcript $t$
extended by $m$ and then $a$; otherwise the outcome is false.

The transcript records only verifier messages and prover replies, so the prover never sees the
verifier's coins. At use sites the cap is polynomial in $|x|$, so polynomial time for each
verifier step gives polynomial total time in the original input.
