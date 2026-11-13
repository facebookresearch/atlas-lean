# Halting on zero reduces to equivalence

The set of codes $c$ of partial recursive
functions on $\mathbb{N}$ that halt on input $0$ (are defined at $0$) is many-one reducible to
the set $EQ$ of pairs of codes with the same domain: there is a computable map $f$ from codes to
pairs of codes such that, for every code $c$, $c$ halts on $0$ if and only if $f(c) \in EQ$.

One can take $f(c) = (h(c), k_0)$, where $h(c)$ runs $c$ on $0$ and then outputs $0$ whatever
its input, and $k_0$ is the code of the constant function $0$.
