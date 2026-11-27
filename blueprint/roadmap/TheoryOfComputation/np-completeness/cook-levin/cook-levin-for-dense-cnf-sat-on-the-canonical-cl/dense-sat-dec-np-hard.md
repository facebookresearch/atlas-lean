# Every NP problem reduces to dense CNF-SAT

Every decision problem $L$ in NP has a
polynomial-time many-one reduction to dense CNF-SAT: a polynomial-time computable map $f$ on bit
strings such that, for every bit string $x$, $L$ accepts $x$ exactly when dense CNF-SAT accepts
$f(x)$.
