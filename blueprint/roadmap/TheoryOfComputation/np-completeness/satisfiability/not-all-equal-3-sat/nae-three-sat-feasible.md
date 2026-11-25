# Not-all-equal satisfiability of an instance

A NOT-ALL-EQUAL 3-SAT instance
$(n, \varphi)$, with $n \in \mathbb{N}$ and $\varphi$ a CNF formula, is not-all-equal satisfiable
when there are truth values $a_0, \dots, a_{n-1}$ such that, for the assignment $v$ with
$v(x) = a_x$ for $x < n$ and $v(x) = \mathrm{false}$ for $x \ge n$, every clause of $\varphi$
contains a literal satisfied by $v$ and a literal not satisfied by $v$.
