# HAMPATH is NP-hard

Every decision problem $L$ in NP has a polynomial-time many-one
reduction to HAMPATH: a polynomial-time computable map $f$ on bit strings such that, for every
bit string $x$, $L$ accepts $x$ exactly when HAMPATH accepts $f(x)$.
