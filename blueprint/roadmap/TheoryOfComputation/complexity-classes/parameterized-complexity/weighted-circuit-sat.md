# Weighted circuit satisfiability with bounded weft and depth

For natural numbers $t$ and
$d$, weighted circuit satisfiability is the parameterized problem that, on a bitstring $x$ and a
parameter $k$, answers true exactly when $x$ decodes to a pair $(n, C)$ of a natural number $n$
and a list $C$ of encoded gates such that: every NOT, AND or OR gate of $C$ references only
strictly earlier gates; every gate of $C$ has weft at most $t$ and depth at most $d$; and there
is an assignment of $n$ Boolean values to the inputs, exactly $k$ of them true, under which $C$
has a last gate and that gate evaluates to true.
