# The pumping lemma for a grammar, with an explicit bound

Let $g$ be a context-free grammar
over an alphabet $T$ and let $R$, $K$, $n$ be natural numbers with $R \ge 2$ such that the
right-hand side of every production of $g$ has length at most $R$, some list of at most $K$
nonterminals contains the left-hand side of every production of $g$, and $R^{K+1} \le n$. Then
every word $w$ in the language of $g$ of length at least $n$ can be written as $w = uvxyz$ with
words $u, v, x, y, z$ over $T$ such that $vy$ is nonempty, $vxy$ has length at most $n$, and
$u v^i x y^i z$ lies in the language of $g$ for every natural number $i$, where $v^i$ is the
concatenation of $i$ copies of $v$.

It follows from Ogden's lemma with every letter marked.
