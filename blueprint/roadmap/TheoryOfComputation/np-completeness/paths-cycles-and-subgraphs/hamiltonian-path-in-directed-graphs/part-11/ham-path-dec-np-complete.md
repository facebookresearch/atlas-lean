# HAMPATH is NP-complete

HAMPATH lies in NP, and every decision problem $L$ in NP has a
polynomial-time many-one reduction to HAMPATH: a polynomial-time computable map $f$ on bit
strings such that, for every bit string $x$, $L$ accepts $x$ exactly when HAMPATH accepts $f(x)$.

## Sources

- Sipser, Theorem 7.46.
