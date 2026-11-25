# Row bits of a formula for the CLIQUE emitter

A literal is a pair $(x, s)$ of a variable
$x \in \mathbb{N}$ and a polarity $s$, and an item is a literal or a clause marker. For a literal
$\ell = (x, s)$, a Boolean $f$ and a list of items, the walk bits are defined by recursion on the
list: there are none for the empty list; for a list starting with a clause marker they are the
walk bits of the rest with $f$ replaced by true; for a list starting with a literal $(x', s')$
they are the bit "$f$ and not ($x = x'$ and $s \ne s'$)" followed by the walk bits of the rest
with the same $f$. For a list $\delta$ of items, the rows of a list of literals are none for the
empty list, and for a list $\ell_1, \dots, \ell_k$ with $k \ge 1$ they are the reverse of the walk
bits of $\ell_1$ with $f$ false over the list $\ell_2, \dots, \ell_k$ followed by $\delta$, then
the rows of $\ell_2, \dots, \ell_k$. The items of a CNF formula $\psi$ are, for each clause of
$\psi$ in order, its literals followed by a clause marker. The row bits of a CNF formula are
defined by recursion on its clauses: the empty formula has none, and for the formula with first
clause $C$ and remaining clauses $\varphi$ they are the rows of the literals of $C$ for $\delta$
the clause marker followed by the items of $\varphi$, followed by the row bits of $\varphi$.
