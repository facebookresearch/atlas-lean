# Counting satisfying assignments of a CNF formula

The counting function $f$ from
bitstrings to natural numbers is defined as follows. If a bitstring $x$ decodes, under the
canonical bitstring encoding of pairs, to a pair $(s, \varphi)$ of a bitstring $s$ of length $n$
and a CNF formula $\varphi$ every literal of which has variable index less than $n$, then $f(x)$
is the number of assignments $a : \{0, \dots, n - 1\} \to \{\mathrm{true}, \mathrm{false}\}$
such that $\varphi$ is satisfied by the assignment sending each variable $v < n$ to $a(v)$ and
every other variable to false. Otherwise $f(x) = 0$.

The bitstring $s$ serves only to give the number of variables $n$ in unary.
