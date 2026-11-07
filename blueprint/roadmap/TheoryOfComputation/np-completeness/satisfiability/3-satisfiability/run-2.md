# Correctness of the clause-length filter

Let $c$ be a Boolean (whether the filter is
capped), $\varphi$ a CNF formula and $v$ an internal state, and let $S$ be stacks holding the
reversed token list of $\varphi$ on the token stack $T$ and nothing on the side stack $U$. Let $b$
be the condition that $c$ is false or every clause of $\varphi$ has at most three literals, and
let $N$ be the number of tokens of $\varphi$. Then the filter program with cap $c$, started at its
start label with internal state $v$ and stacks $S$, reaches within $2N + 2$ steps the label pass
if $b$ holds and the label fail otherwise, with some internal state $v'$ and stacks $S'$; and if
$b$ holds, then $S' = S$.
