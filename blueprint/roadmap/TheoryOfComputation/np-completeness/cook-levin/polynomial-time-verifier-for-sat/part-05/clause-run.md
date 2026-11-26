# Tokenizer run on one clause

A configuration $\langle \ell, v \mid x, w, t, b, i, j\rangle$
of the SAT tokenizer has label $\ell$, internal bit $v$, stacks $X$, $W$, $T$, $B$ holding $x$,
$w$, $t$, $b$ (top first; a bit string stands for its list of bit symbols), and $i$ and $j$ marks
on the clause and literal counters; $\mathbin{+\!\!+}$ is concatenation. Let $C$ be a clause,
$r$ and $w$ bit strings, $t$ and $b$ symbol lists, $c \in \mathbb{N}$ and $v$ a bit. Let $E$ be
the encoding of $C$, $N$ the list of variable indices of the literals of $C$ in order, and $w'$
the string $w$ with its first $|C|$ bits removed (all of them if $w$ is shorter). Then the
tokenizer goes in at most $2|E| + 1$ steps from
$\langle \mathsf{cls}, v \mid E \mathbin{+\!\!+} r, w, t, b, c + 1, 0\rangle$ to
$\langle \mathsf{cls}, \mathsf{false} \mid r, w', \mathrm{rev}(\tau) \mathbin{+\!\!+} t,
\beta \mathbin{+\!\!+} b, c, 0\rangle$, where $\tau$ is the token list of $C$ and $\beta$ is the
table stack of the occurrence table of $N$ against $w$.
