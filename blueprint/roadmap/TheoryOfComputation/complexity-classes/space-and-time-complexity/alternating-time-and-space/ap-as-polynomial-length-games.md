# Alternating polynomial time equals polynomial-length game verification

A language $L$ is in $\mathsf{AP}$ if and only if there are a polynomial $p$, a polynomial-time computable predicate $V(x, m_1, \dots, m_{p(|x|)})$ on single-bit moves, and an assignment of each move index to a player such that

$$
x\in L \iff Q_1 m_1\, Q_2 m_2 \cdots Q_{p(|x|)} m_{p(|x|)}\; V(x,m_1,\dots,m_{p(|x|)})=1,
$$

where $Q_i\in\{\exists,\forall\}$ is the quantifier of the player owning move $i$. In particular $\mathsf{P}\subseteq\mathsf{NP}\subseteq\mathsf{AP}$ (take all moves existential).

## Proof sketch

Given an alternating machine with polynomial clock, the moves are its binary choices and $V$ simulates the deterministic remainder from the recorded choices. Conversely, an alternating machine guesses the moves in the existential or universal states of their owners and then runs $V$ deterministically.

## Depends on

- [Alternating time and space classes ATIME, ASPACE, AP, APSPACE and AL](alternating-time-and-space-classes.md)
- [The complexity class P](../../the-classes-p-np-and-conp/p.md)
- [The complexity class NP](../../the-classes-p-np-and-conp/np.md)

## Sources

- Ashok K. Chandra, Dexter C. Kozen and Larry J. Stockmeyer, "Alternation", Journal of the ACM 28(1), 1981.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
