# HAMPATH is in NP

The [HAMPATH problem](../part-01/ham-path-dec.md), which accepts a bit string $x$ exactly when $x$
is the encoding of a source $s$, a target $t$ and a digraph on $0, \dots, n - 1$ that has a
Hamiltonian path from $s$ to $t$, belongs to NP: there are a polynomial $p$ with natural-number
coefficients and a polynomial-time computable verifier $R$ such that HAMPATH accepts $x$ exactly
when $R(x, w)$ holds for some bit string $w$ with $|w| \le p(|x|)$.
