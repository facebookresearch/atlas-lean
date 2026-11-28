# Conical juntas and their degree

A **conjunction** on $\{0,1\}^n$ is the indicator of a subcube $\{z : z_i = a_i \text{ for } i \in S\}$, of width $|S|$. A **conical junta** is a nonnegative linear combination $h = \sum_C w_C\, C$ of conjunctions with $w_C \ge 0$; its **degree** is the maximum width of a conjunction with $w_C > 0$. The **approximate conical junta degree** $\deg^{+}_{\varepsilon}(f)$ of a Boolean function $f$ is the least degree of a conical junta $h$ with $|h(z) - f(z)| \le \varepsilon$ for all $z$. It satisfies $\deg^{+}_{\varepsilon}(f) \le R_\varepsilon^{dt}(f)$, the bounded-error randomized decision-tree complexity, and it lower-bounds the measure $\mathrm{WAPP}$ in query complexity.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)
- [Certificate complexity, degree and decision-tree depth](../query-and-communication-measures/certificate-complexity-degree-and-decision-tree.md)

## Sources

- M. Göös, S. Lovett, R. Meka, T. Watson, D. Zuckerman, "Rectangles are nonnegative juntas", STOC (2015); SIAM Journal on Computing 45 (2016) 1835-1869.
- M. Göös, T. Pitassi, T. Watson, "Query-to-communication lifting for BPP", FOCS (2017); SIAM Journal on Computing 49 (2020), arXiv:1703.07666.
