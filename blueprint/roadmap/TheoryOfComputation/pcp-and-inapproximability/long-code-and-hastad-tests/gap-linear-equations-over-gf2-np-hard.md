# A constant-gap linear-equations problem over GF(2) is NP-hard

There are constants $1/2 < s < c < 1$ such that it is NP-hard to distinguish systems of linear equations over $\mathbb{F}_2$ (equations counted with multiplicity) in which some assignment satisfies at least a $c$ fraction of the equations from those in which every assignment satisfies fewer than an $s$ fraction. One such pair of thresholds is $c = 4/7$ and $s = \frac{4}{7}\big(1 - \frac{1}{6 \cdot 2^{77}}\big)$, obtained elementarily from the NP-hardness of gap MAX-3SAT by replacing each clause with seven parity equations over subsets of its literals.

## Proof sketch

A 3-clause $\ell_1 \vee \ell_2 \vee \ell_3$ is satisfied iff exactly four of the seven parity equations "the XOR of a nonempty subset of its literals is $1$" hold, and exactly zero hold when it is falsified. So the fraction of satisfied equations is $4/7$ times the fraction of satisfied clauses, and a constant MAX-3SAT gap transfers.

## Depends on

- [NP-complete decision problems](../../complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [Gap 3SAT is NP-hard](../pcp-constructions/gap-3sat-is-np-hard.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
