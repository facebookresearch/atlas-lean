# SUBSET-SUM is in NP

SUBSET-SUM is the decision problem on bit strings that accepts $x$
exactly when $x$ encodes a target $t$ followed by natural numbers $a_1, \dots, a_n$ (each written
in binary and delimited) such that some, possibly empty, sublist of $a_1, \dots, a_n$ sums to
$t$. This decision problem belongs to NP: there are a polynomial $p$ with natural-number
coefficients and a polynomial-time computable verifier $R$ such that SUBSET-SUM accepts $x$
exactly when $R(x, w)$ holds for some bit string $w$ with $|w| \le p(|x|)$.
