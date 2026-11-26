# One round of the list reachability search

Let $s_0 \in \mathbb{N}$, let $\mathrm{next}$
assign to each $s \in \mathbb{N}$ a list $\mathrm{next}(s)$ of natural numbers, and let $B$ and $R$
be lists of natural numbers. The round from $s_0$ with successors $\mathrm{next}$ kept inside $B$
sends the list $R$ of states found so far to the following list: write $s_0$ followed, for each
$s$ in $R$ in order, by $s$ and then the list $\mathrm{next}(s)$; keep the entries that lie in $B$;
then delete every entry that occurs again later in the list.

Its entries are therefore the numbers in $B$ that are $s_0$, an element $s$ of $R$, or an element
of $\mathrm{next}(s)$ for some $s$ in $R$, each listed once.
