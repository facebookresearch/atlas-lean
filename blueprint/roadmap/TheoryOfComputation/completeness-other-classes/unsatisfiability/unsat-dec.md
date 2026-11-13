# UNSAT as a decision problem

The UNSAT decision problem accepts a bitstring $x$ exactly
when $x$ decodes, under the canonical bitstring encoding, to a pair $(n, \varphi)$ of a natural
number $n$ and a CNF formula $\varphi$ such that every variable occurring in $\varphi$ is less
than $n$ and, for every assignment $a$ of booleans to the variables $0, \dots, n - 1$, the
assignment that agrees with $a$ below $n$ and sends every variable $v \ge n$ to false does not
satisfy $\varphi$.
