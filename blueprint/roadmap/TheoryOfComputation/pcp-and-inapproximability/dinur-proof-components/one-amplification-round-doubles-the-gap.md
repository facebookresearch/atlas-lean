# One amplification round doubles the gap

There are constants $C \ge 1$, $\alpha \in (0,1)$ and a fixed alphabet $\Sigma_0$ such that a polynomial-time map $G \mapsto G'$ on constraint graphs over $\Sigma_0$ (preprocessing to a regular expander, killed-walk powering with a fixed walk length, and composition) satisfies: $G'$ is over $\Sigma_0$, $|G'| \le C |G|$, $G'$ is satisfiable iff $G$ is, and $\mathrm{UNSAT}(G') \ge \min\big(2\, \mathrm{UNSAT}(G), \alpha\big)$. Iterating it $O(\log |G|)$ times maps satisfiable graphs to satisfiable graphs and unsatisfiable graphs to graphs with $\mathrm{UNSAT} \ge \alpha$, with polynomial size.

## Proof sketch

Preprocessing loses a constant factor, powering with walk length $t$ gains $\Omega(\sqrt t)$, and composition loses the alphabet-independent constant $\beta$; choosing $t$ large makes the net factor at least $2$ until the gap reaches $\alpha$. Since an unsatisfiable graph has gap at least $1/|E|$, $O(\log|E|)$ rounds suffice, each multiplying the size by a constant.

## Depends on

- [Gap amplification with given constants](../dinur-s-gap-amplification/gap-amplification.md)
- [Preprocessing a constraint graph into a regular expander](../pcp-constructions/preprocessing-a-constraint-graph-into-a-regular.md)

## Proof depends on

- [Gap amplification by killed-walk powering](gap-amplification-by-killed-walk-powering.md)
- [Composition with an assignment tester reduces the alphabet](composition-with-an-assignment-tester.md)

## Sources

- I. Dinur, "The PCP Theorem by Gap Amplification", Journal of the ACM 54(3), 2007.
- J. Radhakrishnan, "Gap Amplification in PCPs Using Lazy Random Walks", ICALP 2006.
