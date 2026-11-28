# Satisfiable bounded-occurrence 3-SAT instances

A bounded-occurrence 3-SAT instance
$(n, \varphi)$ is satisfiable when there is a list $(a_0, \dots, a_{n-1})$ of booleans such that
$\varphi$ is satisfied by the assignment sending each variable $x < n$ to $a_x$ and every
variable $x \ge n$ to false.

The same test is the question of LINEAR SAT, of SAT with at most three literals per clause and at most three clauses per variable, and of 3-SAT with at most five clauses per variable; none of them checks its occurrence or linearity restriction here, only in its well-formedness condition.
