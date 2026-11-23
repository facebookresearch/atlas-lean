# Clauses for a word equation with a length check

For two finite lists of literals $a = a_1 \cdots a_k$ and $b$ (a literal being a pair $(v, s)$ of a variable
$v \in \mathbb{N}$ and a polarity $s$, with negation $\neg(v, s) = (v, \lnot s)$), the equation clauses
are: if $|a| = |b|$, the clauses $\{\neg a_j, b_j\}$ and $\{\neg b_j, a_j\}$ for $j = 1, \dots, k$, in
order; otherwise the single empty clause.
