# Tokenizer run on all clauses

A configuration $\langle \ell, v \mid x, w, t, b, i, j\rangle$
of the SAT tokenizer has label $\ell$, internal bit $v$, stacks $X$, $W$, $T$, $B$ holding $x$,
$w$, $t$, $b$ (top first; a bit string stands for its list of bit symbols), and $i$ and $j$ marks
on the clause and literal counters; $\mathbin{+\!\!+}$ is concatenation. Let $r$ and $w$ be bit
strings, $\varphi$ a CNF formula with $m$ clauses, $t$ and $b$ symbol lists and $v$ a bit. Let
$E$ be the concatenation of the encodings of the clauses of $\varphi$, $N$ the list of variable
indices of all literal occurrences of $\varphi$ in order, and $w'$ the string $w$ with its first
$|N|$ bits removed (all of them if $w$ is shorter). Then the tokenizer goes in at most
$2|E| + m + 1$ steps from $\langle \mathsf{cls}, v \mid E \mathbin{+\!\!+} r, w, t, b, m, 0\rangle$
to $\langle \mathsf{fin}, \mathsf{false} \mid r, w', \mathrm{rev}(\tau) \mathbin{+\!\!+} t,
\beta \mathbin{+\!\!+} b, 0, 0\rangle$, where $\tau$ is the token list of $\varphi$ and $\beta$ is
the table stack of the occurrence table of $N$ against $w$.
