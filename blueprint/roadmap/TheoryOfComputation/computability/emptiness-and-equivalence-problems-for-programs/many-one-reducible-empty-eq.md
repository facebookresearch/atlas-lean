# Emptiness reduces to equivalence

The set $E$ of codes of partial recursive functions
defined on no input is many-one reducible to the set $EQ$ of pairs of codes with the same
domain: there is a computable map $f$ from codes to pairs of codes such that, for every code $c$,
$c \in E$ if and only if $f(c) \in EQ$.

One can take $f(c) = (c, e)$ for a code $e$ defined nowhere.
