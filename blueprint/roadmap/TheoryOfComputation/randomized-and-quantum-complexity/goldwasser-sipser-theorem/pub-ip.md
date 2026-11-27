# Public-coin interactive proofs

A decision problem $L$ is in $\mathsf{PubIP}$ when there
are polynomials $r$, $q$ and $k$ with natural-number coefficients and polynomial-time functions
$V_{\mathrm{msg}}$ (the verifier's message function) and $V_{\mathrm{dec}}$ (its decision
function) with the following property. For a bitstring $x$, a prover $P$ (an arbitrary function
from pairs of a coin prefix and a transcript to bitstrings) and a coin string $c$, let $G(P, c)$
be the outcome of the public-coin interactive-proof game with message length cap $q(|x|)$,
$k(|x|)$ fresh coins per round, verifier $V_{\mathrm{msg}}$ and $V_{\mathrm{dec}}$, prover $P$,
input $x$, coins $c$, $r(|x|)$ remaining rounds out of $r(|x|)$ total rounds and the empty
initial transcript. Then for every bitstring $x$: if $L(x)$ is true, some prover $P$ makes
$G(P, c)$ true for at least $2/3$ of the coin strings $c \in \{0,1\}^{r(|x|) k(|x|)}$; and if
$L(x)$ is false, every prover $P$ makes $G(P, c)$ true for at most $1/3$ of them.
