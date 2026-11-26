# Chen–Huang–Li–Ren: unconditional FP^NP algorithms for ACC0-Avoid and ACC0-RemotePoint

There are unconditional $\mathrm{FP}^{\mathrm{NP}}$ algorithms for:

1. **$\mathrm{ACC}^0$-RemotePoint**: given $C\colon\{0,1\}^n\to\{0,1\}^\ell$ with $\ell=\mathrm{quasipoly}(n)$ in which each output bit is a $\mathrm{quasipoly}(n)$-size $\mathrm{AC}^0[m]$ circuit, output $y\in\{0,1\}^\ell$ whose relative Hamming distance from $C(x)$ is at least $1/2-1/\mathrm{poly}(n)$ for every $x\in\{0,1\}^n$; in particular $\mathrm{ACC}^0$-Avoid is in $\mathrm{FP}^{\mathrm{NP}}$;
2. **$\mathrm{ACC}^0$-AvgPartialHard**: given $x_1,\dots,x_\ell\in\{0,1\}^n$ with $\ell=\mathrm{quasipoly}(n)$, output bits $y_1,\dots,y_\ell$ such that every $\mathrm{ACC}^0$ circuit $C$ of size $2^{\log^{c}n}$ has $\Pr_i[C(x_i)\neq y_i]\ge 1/2-1/\mathrm{poly}(n)$, for a constant $c$.

No $\mathrm{FP}^{\mathrm{NP}}$ algorithm was previously known even for $\mathrm{GF}(2)$-linear circuits or DNF formulas.

## Proof sketch

Williams's polynomial method gives slightly non-trivial Satisfying-Pairs algorithms for $\mathrm{ACC}^0$, via the Beigel–Tarui representation and fast rectangular matrix multiplication; plugging them into the Satisfying-Pairs framework yields the algorithms. They generalize the almost-everywhere average-case lower bounds against $\mathrm{ACC}^0$ of Chen, Lyu and Williams.

## Depends on

- [The class $\mathsf{ACC}^0$](../../time-and-space-complexity-classes/acc0.md)
- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)

## Proof depends on

- [Chen–Huang–Li–Ren: slightly non-trivial Satisfying-Pairs algorithms give FP^NP algorithms for Avoid and Remote Point](satisfying-pairs-to-fpnp-avoid.md)
- [Williams: NEXP is not contained in ACC0](../../../circuit-complexity/williams-nexp-not-in-acc0.md)

## Sources

- Yeyuan Chen, Yizhi Huang, Jiatu Li and Hanlin Ren, "Range Avoidance, Remote Point, and Hard Partial Truth Tables via Satisfying-Pairs Algorithms", STOC (2023), ECCC TR23-072.
