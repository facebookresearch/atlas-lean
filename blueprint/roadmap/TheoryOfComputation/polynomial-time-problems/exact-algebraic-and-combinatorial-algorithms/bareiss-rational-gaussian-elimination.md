# Polynomial-time rational Gaussian elimination (Bareiss)

Given a rational matrix $A$ (entries as reduced fractions in binary) and a rational vector $b$, the following are computable by a deterministic multi-tape Turing machine in time polynomial in the total bit length: the reduced row echelon form of $A$, $\operatorname{rank}A$, a basis of the row space, a basis of the kernel, $\det A$ for square $A$, and a solution of $Ax=b$ or a certificate that none exists. All intermediate numbers have polynomially bounded bit length.

## Proof sketch

Clear denominators row by row and run fraction-free (Bareiss) elimination, in which each update divides exactly by the previous pivot and, by Sylvester's identity, every intermediate entry is (up to sign) a minor of the integer matrix; by Hadamard's inequality, minors have bit length polynomial in the input, so each of the $O(n^3)$ arithmetic operations is polynomial-time.

## Depends on

- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Proof depends on

- [Fraction-free (Bareiss-Jordan) elimination](../../../ComputerScience/algebraic-and-numerical-algorithms/exact-rational-linear-algebra/bareiss-fraction-free-elimination.md)
- [Polynomial bit-length bounds for exact rational elimination](../../../ComputerScience/algebraic-and-numerical-algorithms/exact-rational-linear-algebra/exact-elimination-bit-bounds.md)

## Sources

- Alexander Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986, Theorem 3.3, Corollary 3.3a.
- Erwin H. Bareiss, "Sylvester's Identity and Multistep Integer-Preserving Gaussian Elimination", Mathematics of Computation 22(103), 565–578, 1968.
