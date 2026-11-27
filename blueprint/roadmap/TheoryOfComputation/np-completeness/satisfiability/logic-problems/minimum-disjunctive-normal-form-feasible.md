# Feasible instances of MINIMUM DISJUNCTIVE NORMAL FORM

An instance $(n, A, K)$ is feasible when some DNF expression with at most $K$ disjuncts, all of whose literals refer to variables below $n$, satisfies the following test for every Boolean list $a$ **of length $n$**: the expression is true at $a$ exactly when $a$ is a listed row of $A$. Rows of $A$ of other lengths are never compared: at $n = 1$ and $A = [[\,]]$ the empty DNF passes the test, although its literal set of models is not $\{[\,]\}$.
