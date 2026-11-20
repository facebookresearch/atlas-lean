# The class EXP

EXP, deterministic exponential time, is the class of decision problems
$L$ for which there is a natural number $d$ such that the language of $L$, the set of bitstrings
$x$ with $L(x)$ true, belongs to $\mathrm{DTIME}(2^{n^d})$: it is decided by a multi-tape Turing
machine over the binary alphabet with finitely many states in time at most $c_1 2^{n^d} + c_2$
on inputs of length $n$, for some natural numbers $c_1$ and $c_2$.
