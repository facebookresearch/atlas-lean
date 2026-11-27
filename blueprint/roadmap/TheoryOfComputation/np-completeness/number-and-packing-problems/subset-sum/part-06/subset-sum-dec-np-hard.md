# SUBSET-SUM is NP-hard

Let SUBSET-SUM be the decision problem on bit strings that
accepts exactly the strings encoding a target $t$ followed by natural numbers $a_1, \dots, a_n$
(each written in binary and delimited) such that some, possibly empty, sublist of
$a_1, \dots, a_n$ sums to $t$. Every decision problem $L$ in NP reduces to SUBSET-SUM by a
polynomial-time many-one reduction: there is a polynomial-time computable map $f$ on bit strings
such that, for every bit string $x$, $L$ accepts $x$ exactly when SUBSET-SUM accepts $f(x)$.
