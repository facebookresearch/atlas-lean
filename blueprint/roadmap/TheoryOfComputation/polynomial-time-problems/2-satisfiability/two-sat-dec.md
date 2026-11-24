# 2-SAT as a decision problem

The 2-SAT decision problem accepts a bitstring $x$ exactly
when $x$ decodes, under the canonical bitstring encoding, to a pair $(n, \varphi)$ of a natural
number $n$ and a CNF formula $\varphi$ such that every clause of $\varphi$ has at most two
literals, every variable occurring in $\varphi$ is less than $n$, and there is a list
$(a_0, \dots, a_{n-1})$ of booleans such that $\varphi$ is satisfied by the assignment that
sends each variable $v < n$ to $a_v$ and every other variable to false.
