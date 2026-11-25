# Halting reduces to regularity of halting sets

There is a computable map $f$ from pairs
$(c, n)$ of a partial recursive code and a natural number to partial recursive codes such that for
every pair $(c, n)$, the code $c$ halts on $n$ if and only if the halting set of $f(c, n)$ (the set
of inputs on which it halts), read as a unary language, is regular. That is, halting many-one
reduces to regularity of halting sets.

The construction follows Sipser's proof of Theorem 5.3: $f(c, n)$ halts on every perfect square,
and on every input if $c$ halts on $n$.
