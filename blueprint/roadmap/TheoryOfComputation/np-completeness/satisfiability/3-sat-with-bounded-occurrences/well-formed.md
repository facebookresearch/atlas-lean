# Well-formed bounded-occurrence 3-SAT instances

A bounded-occurrence 3-SAT instance
$(n, \varphi)$ is well formed when every clause of $\varphi$ is a list of exactly three literals,
not necessarily distinct, every literal of $\varphi$ has a variable less than $n$, and for every
variable $v < n$ at most four of the literals in the clauses of $\varphi$, counted with
multiplicity and with either polarity, have variable $v$.
