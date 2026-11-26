# The time-bounded Kolmogorov complexity problem MINKT

*MINKT* is the language of triples $(x, 1^t, 1^s)$ with $K^t(x) \le s$, where the step budget $t$ and the size threshold $s$ are given in unary. For fixed functions $t, s$ computable in polynomial time in unary, $\mathrm{MINKT}[t, s] = \{x : K^{t(|x|)}(x) \le s(|x|)\}$. *MINcKT* is the conditional analogue on inputs $(x, y, 1^t, 1^s)$ asking whether $K^t(x \mid y) \le s$.

## Depends on

- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](time-bounded-kolmogorov-complexity-and-levin-kt.md)

## Sources

- K.-I. Ko, "On the Complexity of Learning Minimum Time-Bounded Turing Machines", SIAM Journal on Computing 20(5), 1991.
- S. Hirahara, "Non-Black-Box Worst-Case to Average-Case Reductions within NP", FOCS 2018.
- Y. Liu and R. Pass, "On One-way Functions and Kolmogorov Complexity", FOCS 2020.
