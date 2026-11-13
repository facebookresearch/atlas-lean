# The rewrites from words with one control symbol are confluent

Let $M$ be a single-tape
Turing machine with finitely many states and tape symbols, and call the states and the halting
symbol $H$ control symbols. Consider the relation in which a word $w$ with exactly one control
symbol rewrites to $w'$ by one step of the rewriting system simulating $M$. This relation is
confluent: if $w$ rewrites in zero or more such steps to both $w_1$ and $w_2$, then $w_1$ and
$w_2$ both rewrite in zero or more such steps to a common word.
