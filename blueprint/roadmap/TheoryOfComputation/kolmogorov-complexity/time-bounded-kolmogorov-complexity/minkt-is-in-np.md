# MINKT and MINcKT are in NP

MINKT and its conditional version MINcKT are in NP. For fixed thresholds $t$ and $s$ computable in polynomial time in unary, $\mathrm{MINKT}[t, s]$ and $\mathrm{MINcKT}[t, s]$ are in NP.

## Proof sketch

A certificate is a program $p$ with $|p| \le s$; the verifier runs the universal machine on $p$ for $t$ steps (on input $y$ in the conditional case) and checks that the output is $x$. Since $t$ and $s$ are in unary, this takes polynomial time.

## Depends on

- [The time-bounded Kolmogorov complexity problem MINKT](the-minkt-problem.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Sources

- K.-I. Ko, "On the Complexity of Learning Minimum Time-Bounded Turing Machines", SIAM Journal on Computing 20(5), 1991.
- S. Hirahara, "Non-Black-Box Worst-Case to Average-Case Reductions within NP", FOCS 2018.
- Y. Liu and R. Pass, "On One-way Functions and Kolmogorov Complexity", FOCS 2020.
