# Levin's optimal universal search

For every relation $R\in\mathsf{PC}$ there is an algorithm $U_R$ that solves the search problem of $R$ on every $x\in S_R$ and is optimal up to a constant factor and an additive polynomial: if some algorithm $A$ finds solutions within time $t_A(x)$, then $U_R$ finds a solution within time $O\bigl(2^{|A|}\,(t_A(x)+p_R(|x|))\bigr)$, where $p_R$ bounds the time to check a candidate. On $x\notin S_R$ the algorithm does not halt (or halts after an exhaustive search).

## Proof sketch

Dovetail all programs: in phase $k$, run program $i\le k$ for $2^{k-i}$ steps on $x$ and check any output with $R$'s polynomial-time verifier. Program $A$ is given a $2^{-|A|}$ fraction of the total time, so once $A$ would have succeeded, the phase sum is within the stated bound.

## Depends on

- [Self-reducible search problems (Goldreich's PC and PF)](self-reducible-search-problems.md)

## Sources

- Leonid A. Levin, "Universal Sequential Search Problems", Problems of Information Transmission 9(3), 1973.
- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Theorem 2.33.
