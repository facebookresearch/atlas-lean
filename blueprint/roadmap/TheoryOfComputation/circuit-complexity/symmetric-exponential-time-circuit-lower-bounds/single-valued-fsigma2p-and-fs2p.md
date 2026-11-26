# Single-valued FΣ2P and FS2P algorithms for search problems

A **single-valued $\mathrm{F}\Sigma_2\mathrm{P}$ algorithm** $A$ is a polynomial $\ell$ and a polynomial-time algorithm $V_A(x,\pi_1,\pi_2)$. On input $x$, $A$ outputs $y_x$ if (1) there is $\pi_1\in\{0,1\}^{\ell(|x|)}$ such that $V_A(x,\pi_1,\pi_2)=y_x$ for every $\pi_2$, and (2) for every $\pi_1$ there is $\pi_2$ with $V_A(x,\pi_1,\pi_2)\in\{y_x,\bot\}$.

A **single-valued $\mathrm{FS}_2\mathrm{P}$ algorithm** replaces (2) by the symmetric condition: there is $\pi_2$ such that $V_A(x,\pi_1,\pi_2)=y_x$ for every $\pi_1$. In both cases $A$ **solves** a search problem $\Pi$ if it outputs some $y_x\in\Pi_x$ on every input $x$. Single-valuedness forces a canonical answer; a single-valued $\mathrm{FZPP}^{\mathrm{NP}}$ algorithm is a zero-error pseudodeterministic algorithm with an $\mathrm{NP}$ oracle.

## Depends on

- [Symmetric alternation: the classes S2TIME[T], S2P and S2E](symmetric-alternation-s2p-s2e.md)
- [Pseudodeterministic algorithms for search problems (Gat–Goldwasser)](../../randomized-and-quantum-complexity/bounded-error-probabilistic-classes-rp-and-bpp/pseudodeterministic-algorithms/pseudodeterministic-algorithm-for-search-problem.md)

## Sources

- Zeyong Li, "Symmetric Exponential Time Requires Near-Maximum Circuit Size: Simplified, Truly Uniform", STOC (2024), arXiv:2310.17762.
- Lijie Chen, Shuichi Hirahara and Hanlin Ren, "Symmetric Exponential Time Requires Near-Maximum Circuit Size", STOC (2024), arXiv:2309.12912.
