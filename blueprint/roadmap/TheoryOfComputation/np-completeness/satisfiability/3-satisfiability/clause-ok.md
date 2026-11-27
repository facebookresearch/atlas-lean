# The 3SAT filter walks one clause within the cap

Let $C$ be a clause, and suppose the cap
flag is off or $C$ has at most three literals. Let $\overline{C}$ be the tokens of $C$ as they
lie on the token stack (the clause marker on top, then the literals' tokens, last literal first),
and let $w_n$ be the walking label after $n$ literals. For every $n$, all lists of symbols $R$
and $U$ and every value $v$ of the Boolean variable, there is a value $v'$ such that the 3SAT
clause-length filter takes exactly $|\overline{C}|$ steps from label $w_n$ with variable $v$,
token stack $\overline{C}$ on top of $R$ and side stack $U$ to label $w_{|C|}$ with variable
$v'$, token stack $R$, and side stack the reversal of $\overline{C}$ on top of $U$.

The clause marker resets the literal count, and each literal then advances it.
