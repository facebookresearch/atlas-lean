# The CYK step

Let $g$ be a context-free grammar in Chomsky normal form, let $f$ assign to
each word over the terminals a finite set of nonterminals, and let $w$ be a nonempty word. For
$0 < i < |w|$ write $u_i$ for the prefix of $w$ of length $i$ and $v_i$ for the remaining suffix,
so that $w = u_i v_i$. Suppose that for every such $i$ and every nonterminal $B$, $B \in f(u_i)$
if and only if $B$ yields $u_i$, and $B \in f(v_i)$ if and only if $B$ yields $v_i$. Then a
nonterminal $A$ lies in the CYK cell of $w$ built from $f$ if and only if $A$ yields $w$.
