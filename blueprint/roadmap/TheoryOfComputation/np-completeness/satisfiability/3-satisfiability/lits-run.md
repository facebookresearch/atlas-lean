# The literals of a clause in the emitter

Write $\langle \ell, w, t, o, z, c\rangle$ for
the configuration of the emitter machine at label $\ell$ with internal variable $w$, token stack
$t$, output stack $o$, fresh counter $z$, output-clause count $c$ and empty scratch stacks. Let
$Z_b$ be a natural number, $L = (l_1, \dots, l_k)$ a list of literals, $R$ a token stack whose
top is a literal marker, $f$ and $v$ Booleans, $o$ an output stack and $z$, $c$ natural numbers
with $z + m \le Z_b$, where $m$ is $k - 1$ (truncated at $0$) if $f$ holds and $k$ otherwise.
The token block of a literal $(n, b)$ is the literal marker of polarity $b$ above the binary
digits of $n$, most significant first (no digits for $n = 0$); let $T$ be the concatenation of
the token blocks of $l_k, \dots, l_1$, in this order. For $1 \le i \le k$ let $z_i = z + m_i$,
where $m_i$ is $k - i - 1$ (truncated at $0$) if $f$ holds and $k - i$ otherwise, let $f_i$ be
true exactly when $f$ holds and $i = k$, and let $e_i$ be the encoding of the output clause of
$l_i$ with flags $f_i$, false and counter $z_i$. Let $E = e_1 \cdots e_k$ (empty for $k = 0$),
and let $f'$ be true exactly when $f$ holds and $k = 0$. Then for some $w'$ the machine goes in
at most $|T| + k (6 Z_b + 14)$ steps from $\langle \mathrm{lit}(f), v, T R, o, z, c\rangle$ to
$\langle \mathrm{lit}(f'), w', R, E\,o, z + m, c + k\rangle$, where juxtaposition is
concatenation of stacks, top first.
