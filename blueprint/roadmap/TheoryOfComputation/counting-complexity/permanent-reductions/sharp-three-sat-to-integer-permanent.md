# #3SAT reduces to the permanent of small-integer matrices

There is a polynomial-time map $\varphi\mapsto M_\varphi$ from 3-CNF formulas with $m$ clauses to square matrices with entries in $\{-1,0,1,2,3\}$ such that

$$
\operatorname{perm}(M_\varphi)=12^{m}\cdot\#\varphi,
$$

where $\#\varphi$ is the number of satisfying assignments of $\varphi$ (over its variables).

## Proof sketch

Valiant's gadget construction: a variable gadget has two cycle covers, one per truth value; each clause gadget, connected to its literals by exchange gadgets, contributes total weight $12$ exactly for each assignment satisfying the clause and $0$ otherwise, so cycle covers inconsistent with an assignment cancel.

## Depends on

- [The 0-1 permanent counts perfect matchings](../complexity-of-the-permanent/permanent-boole-eq-card.md)
- [Counting satisfying assignments of a CNF formula](../counting-satisfiability-sat/count-sat-fun.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Proposition 6.21 and Figure 6.3 (the eight-vertex clause gadget with $c=12$; Valiant's original gadgets give $c=2^{10}$).
- Leslie G. Valiant, "The Complexity of Computing the Permanent", Theoretical Computer Science 8(2), 1979.
