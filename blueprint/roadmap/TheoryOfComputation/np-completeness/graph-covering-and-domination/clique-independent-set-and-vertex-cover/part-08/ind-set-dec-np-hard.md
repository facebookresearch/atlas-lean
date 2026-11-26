# INDEPENDENT-SET is NP-hard

Every decision problem $L$ in NP has a polynomial-time
many-one reduction to INDEPENDENT-SET: a polynomial-time computable map $f$ on bit strings such
that, for every bit string $x$, $L$ accepts $x$ exactly when INDEPENDENT-SET accepts $f(x)$.
