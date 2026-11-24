# Position-wise equality clauses for literal vectors

For two finite lists of literals $a_1 \cdots a_k$ and $b_1 \cdots b_m$ (a literal being a pair $(v, s)$ of a
variable $v \in \mathbb{N}$ and a polarity $s$, with negation $\neg(v, s) = (v, \lnot s)$), the
position-wise equality clauses are defined recursively: for two empty lists there are no clauses; for
two nonempty lists $a_1 \cdots a_k$ and $b_1 \cdots b_m$ they are the clauses $\{\neg a_1, b_1\}$,
$\{\neg b_1, a_1\}$ followed by the clauses for $a_2 \cdots a_k$ and $b_2 \cdots b_m$; and when exactly
one of the lists is empty they are the single empty clause. In particular, lists of different
lengths produce clauses ending in the empty clause, which is unsatisfiable.
