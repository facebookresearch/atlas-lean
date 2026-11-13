# Answer of the SAT host

For a flag $c$ and a pair $(x, w)$ of bit strings, the host's
answer is false if $x$ does not decode to a CNF formula. If $x$ decodes to a formula $\varphi$,
give each variable $n$ the value $w_i$ (counting from $0$), where $i$ is the first position of
$n$ in the list of variable occurrences of $\varphi$ read clause by clause, and the value false
if $i \ge |w|$. Then the answer is true exactly when both (a) $c$ is false or every clause of
$\varphi$ has at most three literals, and (b) every clause of $\varphi$ contains a literal
$(n, b)$ whose variable $n$ has value $b$.
