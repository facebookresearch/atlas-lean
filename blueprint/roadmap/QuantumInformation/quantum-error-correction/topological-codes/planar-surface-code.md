# Planar surface code

Let $L \ge 2$. Take the vertices $(x, y)$ with $x \in \{0, \dots, L - 1\}$ and $y \in \{1, \dots, L - 1\}$, and as edges
(one qubit each): the horizontal edges $(x, y)$–$(x + 1, y)$, $(L - 1)^2$ of them; the vertical edges $(x, y)$–$(x, y + 1)$
for $1 \le y \le L - 2$; and for each $x$ a dangling vertical edge below $(x, 1)$ and one above $(x, L - 1)$. This gives
$(L - 1)^2 + L(L - 2) + 2L = L^2 + (L - 1)^2$ qubits. The check operators are

- for each of the $L(L - 1)$ vertices, $A_s$, the product of $X$ over the edges meeting $s$ (three edges on the left and
  right sides, the smooth boundaries, and four elsewhere);
- for each $x \in \{0, \dots, L - 2\}$ and $y \in \{0, \dots, L - 1\}$, $B_{x,y}$, the product of $Z$ over the edges bounding
  the face between columns $x, x + 1$ and rows $y, y + 1$, where rows $0$ and $L$ lie beyond the dangling edges, so the
  faces with $y = 0$ or $y = L - 1$ have three edges (the top and bottom are the rough boundaries).

The planar surface code is the joint $+1$ eigenspace of these $L(L - 1) + L(L - 1)$ operators. Logical operators are $Z$
along a column of $L$ vertical edges from the bottom to the top rough boundary, and $X$ on the $L$ vertical edges between
two consecutive rows, crossed by a dual path from the left to the right smooth boundary. Dennis, Kitaev, Landahl and
Preskill describe this lattice by its counts and boundaries; the coordinates are one way to fix it.

## Depends on

- [Pauli group, Clifford group and stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-clifford-group-and-stabilizer-states.md)

## Background

- [Toric code](toric-code.md)

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section III.B and Figure 5.
- S. B. Bravyi and A. Yu. Kitaev, *Quantum codes on a lattice with boundary*, arXiv:quant-ph/9811052 (1998), Abstract and introduction.
