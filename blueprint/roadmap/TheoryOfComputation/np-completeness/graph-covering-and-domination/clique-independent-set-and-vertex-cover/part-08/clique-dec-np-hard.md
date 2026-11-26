# CLIQUE is NP-hard

Every decision problem $L$ in NP has a polynomial-time many-one
reduction to CLIQUE: a polynomial-time computable map $f$ on bit strings such that, for every
bit string $x$, $L$ accepts $x$ exactly when CLIQUE accepts $f(x)$.
