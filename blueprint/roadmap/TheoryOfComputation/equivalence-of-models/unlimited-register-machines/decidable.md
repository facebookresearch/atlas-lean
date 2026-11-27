# URM-decidable predicate

A predicate $P$ on the natural numbers is URM-decidable when
some URM program computes its characteristic function: started on any input $n$ (register $0$
holding $n$, all other registers $0$), the program halts, and register $0$ then holds $1$ if
$P(n)$ holds and $0$ otherwise.
