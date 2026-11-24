# One step of the walk over earlier occurrences

Let $l = (x, p)$ be a new occurrence and
$q = (x', b', L', M')$ an earlier one with $M' = L' + 1$. Let $m$ be a quiescent state whose
stack $D$ holds the tokens of $q$ (the marker of polarity $b'$, the name bits of $x'$, then $L'$
unary unit symbols) above a list $S$ whose first symbol, if any, is neither a unary unit nor a
name bit; whose stack $A$ holds the name bits of $x$; whose stack $P$ holds only the marker of
polarity $p$; and whose counter $U$ is $0$. Write $n$ and $r$ for the counters $N$ and $R$ of $m$
and $k$ for the number of tokens of $q$. Then for every local state $v$, the emitter goes from
label walk with state $(v, m)$ to label walk again, with some local state, in at most
$12k + 8(n + r) + 21$ steps. It ends in the state $m$ with $D$ replaced by $S$, with $E$ holding
the tokens of $q$ in reverse order above its old contents, and with the output stack holding
the bits of the consistency edges of $l$ (with literal vertex $n$ and negation vertex $n + 1$)
with $q$ above its old contents.
