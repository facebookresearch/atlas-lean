# Prefix token list of a minus expression

For INEQUIVALENCE OF SIMPLE FUNCTIONS with only the operator $\mathrm{minus}$, an expression is a tree built from variables $x_k$, natural-number constants $c$, and $\mathrm{minus}(e, e')$. Its prefix token list is $[(0, k)]$ for the variable $x_k$, $[(1, c)]$ for the constant $c$, and, for $\mathrm{minus}(e, e')$, the token $(2, 0)$ followed by the token list of $e$ and then that of $e'$. Each token fixes the arity of its operator, so the token list determines the expression.
