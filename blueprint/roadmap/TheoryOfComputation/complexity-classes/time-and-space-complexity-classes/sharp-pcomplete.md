# $\#P$-complete functions

A function $f$ from bitstrings to natural numbers is
$\#P$-complete when $f$ is in $\#P$ and every function $g$ in $\#P$ is computed from $f$ by a
polynomial-time oracle machine. That is, there are polynomials $p$ and $q$ with natural-number
coefficients and polynomial-time computable functions choosing the next query and the final
natural-number answer from the input and the history of queries and oracle answers, such that
for every bitstring $x$ the following outputs $g(x)$: make up to $p(|x|)$ queries to $f$ in
turn, stop early as soon as the next query is longer than $q(|x|)$, and then return the final
answer computed from $x$ and the history.
