# The translation on the remaining clauses

Write $\mathrm{conv}(w, \iota, n, k, m, o)$ for
the reversed-string translation run on the bit string $w$ with open-clause flag $\iota$, literal
count $n$, slot count $k$, clause count $m$ and output $o$; juxtaposition of bit strings is
concatenation, $w^R$ is the reversal of $w$, $1^n$ is $n$ ones and $|x|$ is the length of a list
$x$. For a dense clause $c$, let $E(c)$ be its dense encoding, $c'$ its binary-index translation
with offset $0$, $e(c)$ the concatenation of the binary codes of the literals of $c'$, and $B(c)$
the binary code of the clause $c'$. Let $p, k, m \in \mathbb{N}$, let $c_0, c_1, \dots, c_p$ be
dense clauses and let $D$ be a bit string. Then
$\mathrm{conv}(E(c_1)^R \cdots E(c_p)^R, \mathrm{true}, |c_0'|, k, m, e(c_0)\, D) =
1^{m + p} 0\, B(c_p) \cdots B(c_1) B(c_0) D$.
