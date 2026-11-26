# Copying a renamed name

Write $\langle \ell, w, t, o, z, c\rangle$ for the configuration
of the emitter machine at label $\ell$ with internal variable $w$, token stack $t$, output stack
$o$, fresh counter $z$, output-clause count $c$ and empty scratch stacks. Let $l = (n, b)$ be a
literal, $f$ and $v$ Booleans, $R$ a token stack whose top, if any, is not a bit symbol, $o$ an
output stack and $z$, $c$ natural numbers. Let $B$ be the $k$ binary digits of $n$ as bit
symbols, most significant first ($k = 0$ for $n = 0$), and $e$ the encoding of the renamed
literal $(2n, b)$. Then for some $w'$ the machine goes in exactly $k + 2$ steps from
$\langle \mathrm{body}(f, b), v, B R, o, z, c\rangle$ to
$\langle \mathrm{aft}(f), w', R, e\,o, z, c\rangle$, where juxtaposition is concatenation of
stacks, top first.
