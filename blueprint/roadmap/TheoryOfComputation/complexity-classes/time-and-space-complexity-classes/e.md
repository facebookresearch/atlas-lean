# The class E

E is the class of decision problems $L$ for which there is a natural
number $c$ such that the language of $L$, the set of bitstrings $x$ with $L(x)$ true, belongs to
$\mathrm{DTIME}(2^{cn})$: it is decided by a multi-tape Turing machine over the binary alphabet
with finitely many states in time at most $c_1 2^{cn} + c_2$ on inputs of length $n$, for some
natural numbers $c_1$ and $c_2$.
