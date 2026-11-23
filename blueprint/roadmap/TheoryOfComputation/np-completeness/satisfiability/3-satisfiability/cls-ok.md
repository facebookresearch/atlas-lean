# The 3SAT filter walks a list of clauses within the cap

For a clause $C$ let
$\overline{C}$ be its tokens as they lie on the token stack (the clause marker on top, then the
literals' tokens, last literal first). Let $C_1, \dots, C_k$ be clauses such that, for each $i$,
the cap flag is off or $C_i$ has at most three literals. Let $X$ be the concatenation
$\overline{C_1} \cdots \overline{C_k}$ with $\overline{C_1}$ on top, and let $w_n$ be the walking
label after $n$ literals. For every list of symbols $R$, every $n$, every list of symbols $U$ and
every value $v$ of the Boolean variable, there are $m$ and a value $v'$ such that the 3SAT
clause-length filter takes exactly $|X|$ steps from label $w_n$ with variable $v$, token stack
$X$ on top of $R$ and side stack $U$ to label $w_m$ with variable $v'$, token stack $R$, and side
stack the reversal of $X$ on top of $U$.
