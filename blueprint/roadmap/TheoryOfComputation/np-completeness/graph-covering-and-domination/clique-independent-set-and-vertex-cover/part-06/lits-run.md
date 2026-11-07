# Emitter run over a clause's literals

Write
$\langle \ell, v \mid t, o, a, d, e, c, n\rangle$ for the configuration of the SAT-to-CLIQUE
emitter at label $\ell$ with local bit $v$, stacks $T = t$, $O = o$, $A = a$, $D = d$, $E = e$,
empty scratch stacks $B$ and $X$, and $c$ and $n$ marks on the counters $C$ and $N$;
juxtaposition of lists is concatenation. Let $L, c \in \mathbb{N}$, let $I$ be a list of items
and $\delta$ the concatenation of their tokens, let $l_1, \dots, l_k$ be literals, $R$ a list of
symbols that is empty or does not start with a name-bit symbol, $o$ a list of bits,
$n \in \mathbb{N}$ and $v$ a bit. Let $\lambda_i$ be the token list of $l_i$ as it lies on the
token stack and $\Lambda = |\lambda_1| + \dots + |\lambda_k|$. If $\Lambda + |\delta| \le L$, then
for some bit $v'$ the machine goes in at most $\Lambda (7L + 7)$ steps from
$\langle \mathsf{lits}, v \mid \lambda_k \cdots \lambda_1 R, o, [], \delta, [], c, n\rangle$ to
$\langle \mathsf{lits}, v' \mid R, \rho\, o, [], \delta', [], c, n + k\rangle$, where $\rho$ is the
rows pushed for the literals $l_1, \dots, l_k$ above the items $I$ and $\delta'$ is the
concatenation of the tokens of the items $l_1, \dots, l_k$ followed by those of $I$.
