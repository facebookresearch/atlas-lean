# Efficient reconstruction and complementary programs for monotone span programs

Let $P=(M_i)$ be a monotone span program. (i) For every accepted coalition $S$ one can compute, by Gaussian elimination in time polynomial in the size of $P$, vectors $\lambda_i$ ($i\in S$) with $\sum_{i\in S}\lambda_iM_i=e_1$. (ii) For every coalition $S$ that is not accepted one can compute an invertible change of basis $R$ such that $P_R=(M_iR)$ accepts exactly the same coalitions and every matrix $M_iR$ with $i\in S$ has zero first column. Multiplying all $M_i$ on the right by an invertible matrix $R$ with $e_1R=e_1$ (first row of $R$ equal to $e_1$; in (ii) take $R$ to be the identity with first column replaced by $v$) never changes the accepted coalitions.

## Proof sketch

For (i), solve the linear system for $e_1$ in the row span of the stacked matrices. For (ii), since $e_1$ is not in the row span $W$ of the members, there is a vector $v$ with $\langle w,v\rangle=0$ for $w\in W$ and $v_1=1$; a basis change sending $e_1^\ast$ to $v$ zeroes the first column on $S$ while preserving the span condition.

## Depends on

- [Monotone span programs](monotone-span-programs.md)

## Sources

- Dan Boneh, Victor Shoup, "A Graduate Course in Applied Cryptography", 2023.
