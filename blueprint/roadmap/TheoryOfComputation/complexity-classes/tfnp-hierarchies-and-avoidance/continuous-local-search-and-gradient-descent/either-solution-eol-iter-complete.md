# EITHER-SOLUTION(END-OF-LINE, ITER) is PPAD ∩ PLS-complete

EITHER-SOLUTION(END-OF-LINE, ITER) is complete for $\mathsf{PPAD}\cap\mathsf{PLS}$ under polynomial-time many-one reductions. More generally, EITHER-SOLUTION(A,B) is $\mathsf{PPAD}\cap\mathsf{PLS}$-complete whenever $A$ is PPAD-complete and $B$ is PLS-complete.

## Proof sketch

Membership in PPAD: ignore $I_B$ and reduce $I_A$ to END-OF-LINE; any END-OF-LINE solution maps back to a solution of $I_A$, which is a valid output. Membership in PLS is symmetric using $I_B$. Hardness: if $R\in\mathsf{PPAD}\cap\mathsf{PLS}$ there are reductions $(f_A,g_A)$ from $R$ to $A$ and $(f_B,g_B)$ from $R$ to $B$; map $x\mapsto(f_A(x),f_B(x))$ and map an answer back with $g_A$ or $g_B$ according to which instance it solves.

## Depends on

- [ITER and the EITHER-SOLUTION combinator for building PPAD ∩ PLS-complete problems](iter-and-either-solution.md)

## Sources

- John Fearnley, Paul W. Goldberg, Alexandros Hollender and Rahul Savani, "The Complexity of Gradient Descent: CLS = PPAD ∩ PLS", STOC (2021) and Journal of the ACM 70(1) (2023), arXiv:2011.01929.
- Constantinos Daskalakis and Christos H. Papadimitriou, "Continuous Local Search", SODA (2011).
