# Decision-tree depth is at most certificate complexity times block sensitivity

For every Boolean function $f:\{0,1\}^n\to\{0,1\}$, $D(f)\le C(f)\cdot bs(f)$. Since $C(f)\le s(f)\,bs(f)\le bs(f)^2$, consequently $D(f)\le bs(f)^3$.

## Proof sketch

The tree works in rounds. In each round it picks a $1$-certificate consistent with all answers so far and queries all its at most $C(f)$ unqueried variables; if the answers agree with the certificate, it outputs $1$, and if no $1$-input remains consistent, it outputs $0$. Suppose that after $bs(f)$ rounds both a $0$-input $z$ and a $1$-certificate remain consistent with the answers. For each round, and for that remaining certificate, the positions where $z$ disagrees with the certificate are unqueried before it, so they form $bs(f)+1$ disjoint blocks, and flipping $z$ on any one of them satisfies a $1$-certificate. These are disjoint sensitive blocks of $z$, a contradiction; so at most $bs(f)$ rounds are needed.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Proof depends on

- [Certificate complexity, degree and decision-tree depth](../query-and-communication-measures/certificate-complexity-degree-and-decision-tree.md)

## Sources

- N. Nisan, "CREW PRAMs and Decision Trees", SIAM Journal on Computing 20(6), 1991.
- R. Beals, H. Buhrman, R. Cleve, M. Mosca and R. de Wolf, "Quantum Lower Bounds by Polynomials", Journal of the ACM 48(4), 2001.
