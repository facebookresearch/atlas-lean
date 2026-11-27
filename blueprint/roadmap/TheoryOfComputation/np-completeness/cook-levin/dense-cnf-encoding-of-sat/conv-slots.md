# The translation on the slots of a clause

Write $\mathrm{conv}(w, \iota, n, k, m, o)$ for
the reversed-string translation run on the bit string $w$ with open-clause flag $\iota$, literal
count $n$, slot count $k$, clause count $m$ and output $o$; juxtaposition of bit strings is
concatenation, $w^R$ is the reversal of $w$ and $|x|$ is the length of a list $x$. Let $c$ be a
dense clause, $r$ and $o$ bit strings and $n, k, m \in \mathbb{N}$. Let $s(c)$ be the
concatenation of the two-bit codes of the slots of $c$, let $c'$ be the binary-index translation
of $c$ with offset $k$, and let $e$ be the concatenation of the binary codes of the literals of
$c'$. Then
$\mathrm{conv}(s(c)^R r, \mathrm{true}, n, k, m, o) =
\mathrm{conv}(r, \mathrm{true}, n + |c'|, k + |c|, m, e\, o)$.
