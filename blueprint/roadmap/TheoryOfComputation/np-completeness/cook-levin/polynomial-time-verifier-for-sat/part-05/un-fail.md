# An unterminated unary count is rejected

Let $r$ be a bit string on which reading a unary
length prefix fails. For every bit $c$, symbol lists $w, t, b$, counter values $m, \ell$ and
value of the Boolean variable, the tokenizer started at the label $\mathrm{un}(c)$ with $X$
holding the bits of $r$, with $W$, $T$, $B$ holding $w$, $t$, $b$, and with the counters $CC$
and $LC$ holding $m$ and $\ell$ in unary reaches the rejecting label within $|r| + 1$ steps.
