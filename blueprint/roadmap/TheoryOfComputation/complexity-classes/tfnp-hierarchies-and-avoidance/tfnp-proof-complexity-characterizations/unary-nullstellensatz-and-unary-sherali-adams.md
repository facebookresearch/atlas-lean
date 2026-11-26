# Unary Nullstellensatz and unary Sherali–Adams refutations of CNF formulas

Encode a clause $C$ by the polynomial $\overline C$ that equals $1$ exactly on assignments falsifying $C$ (the product of the negated literals), and work multilinearly, modulo $x_j^2=x_j$. Recall that a Nullstellensatz refutation over a field $\mathbb F$ of polynomial equations $a_i=0$ is a family $p_i$ with $\sum_ip_ia_i=1$, with degree $\max_i(\deg p_i+\deg a_i)$ and size the total number of monomials.

A **unary Nullstellensatz (uNS)** refutation of $F$ is an identity $\sum_{i=1}^mp_i\overline{C_i}=1$ with integer coefficients written in unary; its size is the sum of the magnitudes of all coefficients.

A **Sherali–Adams (SA)** refutation is an identity $\sum_ip_i\overline{C_i}=1+J$ over $\mathbb R$, where $J=\sum_j\alpha_jt_j$ is a **conical junta**: $\alpha_j\ge0$ and each $t_j$ a conjunction of literals. A **unary Sherali–Adams (uSA)** refutation is an SA refutation with integer coefficients written in unary, size being the total magnitude. Every uSA refutation can be normalised to the form $\sum_iJ_i\overline{C_i}=1+J_0$ with all $J_i$ conical juntas, without increasing degree or size.

## Depends on

- [Pebble games with counting and the Sherali–Adams hierarchy](../../../descriptive-complexity/pebble-games-with-counting.md)

## Sources

- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao, "Separations in Proof Complexity and TFNP", FOCS (2022) and Journal of the ACM 71(4) (2024), arXiv:2205.02168.
