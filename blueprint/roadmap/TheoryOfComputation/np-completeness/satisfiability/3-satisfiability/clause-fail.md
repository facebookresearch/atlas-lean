# A clause with more than three literals makes the capped 3SAT filter fail

Let $C$ be a
clause with more than three literals, let $\overline{C}$ be its tokens as they lie on the token
stack (the clause marker on top, then the literals' tokens, last literal first), and let $w_n$ be
the walking label after $n$ literals. For every $n$, all lists of symbols $R$ and $U$ and every
value $v$ of the Boolean variable, the 3SAT clause-length filter with the cap on reaches label
$\mathsf{fail}$, with some value of the variable and some stacks, in at most $|\overline{C}|$
steps from label $w_n$ with variable $v$, token stack $\overline{C}$ on top of $R$, and side
stack $U$.
