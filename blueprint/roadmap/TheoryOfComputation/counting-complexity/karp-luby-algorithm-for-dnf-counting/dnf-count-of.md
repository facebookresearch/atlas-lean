# Number of satisfying assignments of an encoded DNF formula

For a bitstring $x$: if $x$
decodes, under the canonical bitstring encoding, to a pair $(u, \varphi)$ of a bitstring $u$ of
length $m$ and a DNF formula $\varphi$ all of whose literals have variables less than $m$, the
value at $x$ is the number of assignments of booleans to the variables $0, \dots, m - 1$ that
satisfy $\varphi$; otherwise the value is $0$.
