# Oblivious MAX-E3SAT approximation from a three-wise independent sample space

There is a polynomial-time map sending $n \ge 1$ variables to fewer than $4n$ assignments of them such that, for every CNF formula over these variables whose clauses have at least $k \le 3$ distinct literals, one of the listed assignments satisfies at least a $1 - 2^{-k}$ fraction of the clauses. In particular one of them satisfies at least $7/8$ of the clauses of every exact-3-CNF formula on these variables. The list does not depend on the formula; the guarantee fails for $k = 4$ because the space is not four-wise independent.

## Proof sketch

Use the linear sample space $x_i = \langle s, v_i \rangle$ over $\mathbb{F}_2$ with vectors $v_i$ any three of which are linearly independent (e.g. $v_i = (1, i)$ in binary with an extra coordinate making sums distinct); it has fewer than $4n$ seeds and the bits are three-wise independent, so the expected fraction of satisfied clauses with at most three literals equals that under uniform assignments, and some seed attains the expectation.

## Depends on

- [The MAX-3SAT objective](../approximability-of-max-3sat/max3-satval.md)

## Sources

- N. Alon and J. H. Spencer, "The Probabilistic Method", 4th ed., Wiley, 2016.
