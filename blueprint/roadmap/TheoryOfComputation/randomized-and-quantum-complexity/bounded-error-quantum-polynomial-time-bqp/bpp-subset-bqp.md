# BPP is contained in BQP

Every language in BPP (decided with error at most $1/3$ by a probabilistic polynomial-time verifier)
is in BQP (decided with error at most $1/3$ by a uniform family of polynomial-size quantum circuits).
Prepare the random string in an equal superposition, run a reversible version of the verifier and
measure its output bit; the acceptance probability is unchanged.

Bernstein and Vazirani prove this for quantum Turing machines (Theorem 8.2.2 in the author-hosted
version dated September 8, 1997). BQP is defined here by circuits
whose gates are 2-local unitaries with rational entries, so this proof also needs reversible circuits
of such gates for polynomial-time functions (Toffoli gates from controlled-$\sqrt{\mathrm{NOT}}$ and
CNOT gates) and unbiased coins from $\sqrt{\mathrm{NOT}}$.

## Background

- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md): the verifier definition used here.
- [BQP](../../complexity-classes/time-and-space-complexity-classes/bqp.md): the circuit definition used here.
- [BQP is contained in PSPACE](bqp-subset-pspace.md): the upper bound proved in the same paper.

## Sources

- E. Bernstein and U. Vazirani, "Quantum complexity theory", SIAM Journal on Computing 26 (1997), 1411–1473; author-hosted version dated September 8, 1997 (https://people.eecs.berkeley.edu/~vazirani/pubs/bv.pdf), Theorem 8.2.2 (theorem number as in that version).
