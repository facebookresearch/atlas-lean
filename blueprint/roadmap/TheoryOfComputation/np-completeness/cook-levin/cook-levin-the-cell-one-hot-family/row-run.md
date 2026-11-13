# Generator run over one row of at-most-one clauses

Let $L$ be a layout with $g$ symbol
codes, let $V$ and $B$ be natural numbers with $B + g \le V$, write $p_i$ for the variable with
index $i$, and let $F$ assign a value to each counter of the one-hot generator such that the
scratch counters are empty ($\mathrm{Rest}(F)$), $F(CB) = B$, $F(Vc) = V$ and $F(P) = 0$. Let
$y < g$, let $\beta = V(3V + 6) + g(6V + 9) + 3V + 4$ be the step budget of one clause, and for
$x' < y$ let $e_{x'}$ be the encoding of the dense clause over $V$ variables whose only literals
are $\lnot p_{B + x'}$ and $\lnot p_{B + y}$. Then for every $x < y$, every output list $o$ and
every flag $v$, the one-hot generator of $L$, started at the label of the at-most-one clause for
the pair $(x, y)$ with flag $v$, output stack $o$ and each counter $c$ holding $F(c)$, reaches
within $(x + 1) \beta$ steps the label $\mathrm{yDone}(y)$ (Y Done) with flag false, the same
counters, and output stack $e_0 e_1 \cdots e_x \, o$ (concatenation).
