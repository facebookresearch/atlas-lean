# The 1-in-3-SAT decision problem

The 1-in-3-SAT decision problem accepts a bitstring $x$
exactly when $x$ decodes, under the canonical bitstring encoding, to a pair $(n, \varphi)$ of a
natural number $n$ and a CNF formula $\varphi$ such that every clause of $\varphi$ has exactly
three literals, every literal $(y, b)$ of $\varphi$ has variable index $y < n$, and some
assignment $v$ of truth values to the variables $0, \dots, n - 1$ makes exactly one position
of every clause hold a literal $(y, b)$ with $v(y) = b$. It rejects every bitstring that does
not decode.
