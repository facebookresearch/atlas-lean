# A long clause makes the capped 3SAT filter fail on a list of clauses

For a clause $C$ let
$\overline{C}$ be its tokens as they lie on the token stack (the clause marker on top, then the
literals' tokens, last literal first). For a list of clauses $C_1, \dots, C_k$, let $X$ be the
concatenation $\overline{C_1} \cdots \overline{C_k}$ with $\overline{C_1}$ on top, and let $w_n$
be the walking label after $n$ literals. If some $C_i$ has more than three literals, then for
every list of symbols $R$, every $n$, every list of symbols $U$ and every value $v$ of the Boolean
variable, the 3SAT clause-length filter with the cap on reaches label $\mathsf{fail}$, with some
value of the variable and some stacks, in at most $|X|$ steps from label $w_n$ with variable $v$,
token stack $X$ on top of $R$, and side stack $U$.
