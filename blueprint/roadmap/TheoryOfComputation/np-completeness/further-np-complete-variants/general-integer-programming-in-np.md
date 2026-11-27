# Integer programming with unbounded integer variables is in NP

Feasibility of a system $Ax\le b$ with $A\in\mathbb{Z}^{m\times n}$, $b\in\mathbb{Z}^{m}$ over $x\in\mathbb{Z}^{n}$ (no bounds on the variables) is in $\mathsf{NP}$, and $\mathsf{NP}$-complete, since 0-1 integer programming feasibility reduces to it by adding the constraints $0\le x_i\le1$. If the system has an integer solution, it has one whose entries are bounded in absolute value by $(2n+m)(ma)^{2m+1}$, where $a\ge1$ bounds the absolute values of the entries of $A$ and $b$, so that solutions have polynomially many bits.

## Proof sketch

Write $x=x^{+}-x^{-}$ and add slack variables: $Ax\le b$ has an integer solution iff $Ax^{+}-Ax^{-}+s=b$ has a nonnegative integer solution, a system in standard form with $m$ rows, $2n+m$ columns and entries bounded by $a$. Papadimitriou's small-solution lemma for standard form (a feasible system $A'x'=b$, $x'\ge0$ integral, with $m$ rows and $n'$ columns has an integral solution with entries at most $n'(ma)^{2m+1}$; Cramer's rule bounds the relevant subdeterminants by $(ma)^{m}$) gives the bound. The NP certificate is such a solution.

## Depends on

- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [0-1 INTEGER PROGRAMMING FEASIBILITY is NP-complete](../number-and-packing-problems/0-1-integer-programming/zero-one-ilp-np-complete.md)

## Sources

- Christos H. Papadimitriou, "On the Complexity of Integer Programming", Journal of the ACM 28(4), 765–768, 1981.
- Alexander Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986, Chapter 17.
