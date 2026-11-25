# Values of simple-function expressions

Under an assignment $a$ of natural numbers to the variables, an expression evaluates by: $x_k
\mapsto a(k)$; $s(e) = e + 1$; $p(e) = \max(e - 1, 0)$; $\mathrm{plus}(e, e') = e + e'$;
$\mathrm{div}(e, t) = \lfloor e / t \rfloor$, which is $0$ when $t = 0$; $\mathrm{mod}(e, t)$ is
the remainder of $e$ modulo $t$, which is $e$ when $t = 0$; $w(e, e') = e$ if $e' = 0$ and $0$
otherwise; and $\mathrm{select}_i(e_1, \dots, e_n) = e_{\max(i-1, 0) + 1}$, the entry at
position $\max(i - 1, 0)$ counting from $0$, so that $\mathrm{select}_0$ and $\mathrm{select}_1$
both give $e_1$, and the value is $0$ when that position is beyond the list.
