# Leftmost derivation

Let $g$ be a context-free grammar, $u$ a sentential form of $g$, $w$ a
word of terminals and $r_1, \dots, r_n$ a list of rules over the terminals and nonterminals of
$g$. The list $r_1, \dots, r_n$ is a leftmost derivation of $w$ from $u$ in $g$ when every $r_i$
is a production of $g$, and, starting from $u$ and for $i = 1, \dots, n$ in turn, the leftmost
nonterminal of the current sentential form is the left-hand side of $r_i$ and is replaced by the
right-hand side of $r_i$, and the sentential form reached after these $n$ steps is $w$, read as a
string of terminals. In particular the empty list is a leftmost derivation of $w$ from $u$
exactly when $u$ is $w$ read as a string of terminals.
