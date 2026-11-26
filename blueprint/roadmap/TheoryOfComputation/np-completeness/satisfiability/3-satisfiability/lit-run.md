# One literal of the emitter

Write $\langle \ell, w, t, o, z, c\rangle$ for the
configuration of the emitter machine at label $\ell$ with internal variable $w$, token stack $t$,
output stack $o$, fresh counter $z$, output-clause count $c$ and empty scratch stacks. Let
$l = (n, b)$ be a literal, $f$ and $v$ Booleans, $R$ a token stack whose top, if any, is not a
bit symbol, $o$ an output stack, and $z$, $c$, $Z_b$ natural numbers with $z + d \le Z_b$, where
$d = 0$ if $f$ holds and $d = 1$ otherwise. Let $T_l$ be the token block of $l$: the literal
marker of polarity $b$ above the binary digits of $n$, most significant first (no digits for
$n = 0$). Let $g$ be true exactly when the top of $R$ is not a literal marker (in particular
when $R$ is empty), let $\ell'$ be $\mathrm{start}$ if $g$ holds and $\mathrm{lit}(\text{false})$
otherwise, and let $e$ be the encoding of the output clause of $l$ with flags $f$, $g$ and
counter $z$. Then for some $w'$ the machine goes in at most $|T_l| + 6 Z_b + 14$ steps from
$\langle \mathrm{lit}(f), v, T_l R, o, z, c\rangle$ to
$\langle \ell', w', R, e\,o, z + d, c + 1\rangle$, where juxtaposition is concatenation of
stacks, top first.
