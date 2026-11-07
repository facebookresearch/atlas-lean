# Generator run over the first rows and the at-least-one clause

Let $L$ be a layout with
$g$ symbol codes, let $V$ and $B$ be natural numbers with $B + g \le V$, write $p_i$ for the
variable with index $i$, and let $F$ assign a value to each counter of the one-hot generator such
that the scratch counters are empty ($\mathrm{Rest}(F)$), $F(CB) = B$, $F(Vc) = V$ and
$F(P) = 0$. Let $\beta = V(3V + 6) + g(6V + 9) + 3V + 4$ be the step budget of one clause, and
for $y \le g$ let $e_y$ be the encoding of the CNF formula whose first clause is the dense clause
over $V$ variables with the positive literals $p_B, \dots, p_{B + g - 1}$, followed by the
at-most-one clauses of the rows $y' < y$ with base $B$ over $V$ variables (Rows CNF). Then for
every $y \le g$, every output list $o$ and every flag $v$, the one-hot generator of $L$, started
at the label $\mathrm{yDone}(y)$ (Y Done) with flag $v$, output stack $o$ and each counter $c$
holding $F(c)$, reaches within $(1 + y^2) \beta$ steps the label $\mathrm{jd}$ (which drains
$CB$) with flag false, the same counters, and output stack $e_y \, o$ (concatenation).
