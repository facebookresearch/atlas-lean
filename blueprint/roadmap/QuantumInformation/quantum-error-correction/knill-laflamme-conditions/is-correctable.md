# Correctable errors on a quantum code

Let $P$ be the orthogonal projector onto a code $C$ in $\mathbb{C}^n$ and let $A_a$ be a
family of error operators on $\mathbb{C}^n$. The errors are *correctable* on $C$ if there are
finitely many matrices $R_1, \dots, R_N$ with $\sum_r R_r^{*} R_r = I$, the Kraus operators of
a recovery channel, and scalars $\lambda_{ra}$ with

$$R_r A_a P = \lambda_{ra} P \quad \text{for all } r, a.$$

After the error $A_a$ and the recovery, every code state is thus restored up to a scalar. The
error operators need not satisfy $\sum_a A_a^{*} A_a = I$.

Knill and Laflamme define an $\mathcal{A}$-correcting code $(C, \mathcal{R})$ by the vanishing
of the error $E(C, \mathcal{R}\mathcal{A})$; their Theorem 3.1 shows that this holds exactly
when each $R_r A_a$ restricted to $C$ is a multiple of the identity, which is the condition
used here.

## Sources

- E. Knill and R. Laflamme, *Theory of quantum error-correcting codes*, Phys. Rev. A 55 (1997), 900–911, arXiv:quant-ph/9604034, Section 3.1 and Theorems 3.1–3.2.
