# Four-clause gadget from 3-variable XOR constraints to exact 3-CNF

Each linear equation $x_1 \oplus x_2 \oplus x_3 = b$ over three distinct variables is equivalent to the conjunction of the four 3-clauses on $x_1, x_2, x_3$ that exclude exactly the four assignments violating it. An assignment satisfying the equation satisfies all four clauses, and an assignment violating it falsifies exactly one of them. Hence if a system of $m$ such equations has optimum fraction $\mathrm{OPT}$, the resulting $4m$-clause exact-3-CNF formula has optimum fraction $1 - (1 - \mathrm{OPT})/4$.

## Proof sketch

The four violating assignments of a parity constraint on three bits are pairwise at Hamming distance two, so each is excluded by its own clause, and any assignment falsifies at most the clause excluding it.

## Depends on

- [The MAX-3SAT objective](../approximability-of-max-3sat/max3-satval.md)

## Sources

- J. Håstad, "Some Optimal Inapproximability Results", Journal of the ACM 48(4), 2001, proof of Theorem 6.1.
