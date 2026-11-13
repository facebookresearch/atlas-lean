# The return loop of the lookup machine

Let $t$ and $w$ be lists of symbols, let $pre$ and
$post$ be lists of table entries, and let $m$ be the total number of symbols of the entries of
$post$. Suppose the lookup program is at label $\mathsf{back}$, with any internal bit, and its
stacks are: $T$ holds $t$; $B$ holds the table stack of $pre$; $S$ holds the symbols of the
entries of $post$ in reading order, first entry on top; $A$ and $C$ are empty; and $V$ holds $w$.
Then within $2m + 2$ steps the program reaches label $\mathsf{done}$, with some internal bit,
where $B$ holds the table stack of the entry list $pre$ followed by $post$, the stacks $S$, $A$
and $C$ are empty, and $T$ and $V$ still hold $t$ and $w$.
