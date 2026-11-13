# The translation on a whole clause

Write $\mathrm{conv}(w, \iota, n, k, m, o)$ for the
reversed-string translation run on the bit string $w$ with open-clause flag $\iota$, literal count
$n$, slot count $k$, clause count $m$ and output $o$; juxtaposition of bit strings is
concatenation, $w^R$ is the reversal of $w$, $1^n$ is $n$ ones and $|x|$ is the length of a list
$x$. Let $c$ be a dense clause, $r$ and $o$ bit strings, $\iota$ a truth value and
$n, k, m \in \mathbb{N}$. Let $E(c)$ be the dense encoding of $c$ (its slot codes followed by the
terminator $00$), $c'$ the binary-index translation of $c$ with offset $0$, and $e$ the
concatenation of the binary codes of the literals of $c'$. Put $o' = 1^n 0\, o$ if $\iota$ is true
and $o' = o$ otherwise. Then
$\mathrm{conv}(E(c)^R r, \iota, n, k, m, o) =
\mathrm{conv}(r, \mathrm{true}, |c'|, |c|, m + 1, e\, o')$.
