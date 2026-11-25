# The mismatch productions

**The mismatch productions** of a nonterminal $A$ for one side of a list $P$ of dominoes over a
finite alphabet. Let $s$ be a map from dominoes to words (in use, the top or the bottom). For each
index $i < |P|$ write $w = s(d_i)$ for the $i$-th domino $d_i$ of $P$ and $\mathrm{code}(i)$ for
the unary code of $i$ as bits. With letters and bits as terminals and $N_3$, $N_4$, $N_7$ the
nonterminals $3$, $4$, $7$ (meant to generate words of letters, nonempty words of letters and
codes of indices), the productions are $A \to w\,A\,\mathrm{code}(i)$ and
$A \to w\,N_4\,\mathrm{code}(i)$, which peel $w$ off, and, for each proper prefix $u$ of $w$,
$A \to u\,N_7\,\mathrm{code}(i)$ and $A \to u\,a\,N_3\,N_7\,\mathrm{code}(i)$ for every letter $a$
other than the letter of $w$ following $u$, which stop matching.
