# Le Gall-Nishimura-Thakkar: Order Verification is in QCMA

For black-box groups with unique encoding, Order Verification is in $\mathrm{QCMA}$: there is a polynomial-time quantum verifier which, given generators of $H \le G$, an integer $N$ and a classical witness of polynomial length, accepts with probability at least $2/3$ for some witness if $|H| = N$ and with probability at most $1/3$ for every witness if $|H| \ne N$. Consequently Group Non-Membership is in $\mathrm{QCMA}$, resolving a question of Watrous (2000) and confirming a conjecture of Aaronson and Kuperberg (2006).

## Proof sketch

The classical witness describes a composition series of $H$ by short straight-line programs together with claimed orders of the composition factors. Each factor is verified quantumly: abelian sections by Shor-type order finding and hidden subgroup algorithms, and non-abelian simple factors by recognizing their isomorphism type via classical certificates combined with quantum order computations. Multiplying verified factor orders checks $|H| = N$; non-membership of $g$ follows by comparing $|\langle H, g\rangle|$ with $|H|$.

## Depends on

- [The class QCMA of quantum verification with classical witnesses](quantum-classical-merlin-arthur.md)
- [Black-box groups, Group Non-Membership and Order Verification](black-box-groups-and-group-problems.md)

## Proof depends on

- [Watrous: Group Non-Membership is in QMA](group-non-membership-in-qma.md)

## Sources

- Francois Le Gall, Harumichi Nishimura, Dhara Thakkar, "Group order is in QCMA", FOCS (2025); arXiv:2504.05547.
- Scott Aaronson, Greg Kuperberg, "Quantum versus classical proofs and advice", Theory of Computing 3 (2007), CCC (2007); arXiv:quant-ph/0604056.
