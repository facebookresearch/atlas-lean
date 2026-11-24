# Bounded reachability search on lists of states

Let $s_0 \in \mathbb{N}$, let
$\mathrm{next}$ assign to each $s \in \mathbb{N}$ a list $\mathrm{next}(s)$ of natural numbers, and
let $B$ be a list of natural numbers. One search round sends a list $R$ to the list obtained by
writing $s_0$ followed, for each $s$ in $R$ in order, by $s$ and then the list $\mathrm{next}(s)$,
keeping the entries that lie in $B$, and deleting every entry that occurs again later; its entries
are the elements of $B$ that are $s_0$, an element of $R$, or an element of $\mathrm{next}(s)$ for
some $s$ in $R$, each listed once. The search returns the result of applying this round $|B|$
times to the empty list, where $|B|$ is the length of $B$.

When $B$ contains $s_0$ and is closed under $\mathrm{next}$, a number is an entry of the returned
list exactly when it is reachable from $s_0$ by finitely many, possibly zero, steps from some $s$
to an element of $\mathrm{next}(s)$.
