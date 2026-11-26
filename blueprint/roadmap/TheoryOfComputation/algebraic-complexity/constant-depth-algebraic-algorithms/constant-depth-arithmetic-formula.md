# Constant-depth arithmetic formulas with unbounded fan-in (arithmetic AC0)

Over a field $\mathbb{F}$, a **constant-depth arithmetic formula** of depth $\Delta$ and size $s$ is a formula whose gates are unbounded fan-in addition and multiplication gates (with field constants on edges) arranged in at most $\Delta$ alternating layers, with $s$ gates in total. A family $\{f_n\}$ of polynomial maps is in **arithmetic $\mathrm{AC}^0$** if it is computed by formulas of size $\operatorname{poly}(n)$ and depth $O(1)$. Multiple outputs are allowed, each computed by its own formula.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Sources

- R. Andrews, A. Wigderson, "Constant-depth arithmetic circuits for linear algebra problems", FOCS (2024), arXiv:2404.10839.
- N. Limaye, S. Srinivasan, S. Tavenas, "Superpolynomial lower bounds against low-depth algebraic circuits", FOCS (2021); Communications of the ACM 65 (2022), ECCC TR21-081.
