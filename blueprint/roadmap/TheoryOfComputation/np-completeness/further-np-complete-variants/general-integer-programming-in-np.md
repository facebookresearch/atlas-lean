# Integer programming with unbounded integer variables is in NP

Feasibility of a system $Ax\le b$ with $A\in\mathbb{Z}^{m\times n}$, $b\in\mathbb{Z}^{m}$ over $x\in\mathbb{Z}^{n}$ (no bounds on the variables) is in $\mathsf{NP}$, and hence $\mathsf{NP}$-complete. If the system has an integer solution, it has one whose entries are bounded in absolute value by $n(ma)^{2m+1}$, where $a$ bounds the absolute values of the entries of $A$ and $b$, so that solutions have polynomially many bits.

## Proof sketch

Small-solution theorem: an integer point of a rational polyhedron can be written as a combination of a vertex-sized point and bounded multiples of generators of the recession cone; Cramer's rule bounds the determinants involved by $(ma)^{m}$, giving the stated bound. The NP certificate is such a solution.

## Depends on

- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Sources

- Christos H. Papadimitriou, "On the Complexity of Integer Programming", Journal of the ACM 28, 1981.
- Alexander Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.
