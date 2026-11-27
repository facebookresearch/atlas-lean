# Hilbert's tenth problem over a ring

Hilbert's tenth problem over a commutative ring $R$, with coefficients from a countable subring $A$, is the decision problem that asks, for a polynomial with coefficients in $A$, whether it has a zero all of whose coordinates lie in $R$.

Let $R$ be a commutative ring with $1$ and let $A \subseteq R$ be a countable subring, together with a fixed encoding of the elements of $A$ as finite strings over a finite alphabet under which the set of codes is decidable and equality, addition and multiplication in $A$ are computable on codes. An instance of *Hilbert's tenth problem over $R$ with coefficients in $A$* is a number $n \ge 1$ of unknowns and a polynomial $f \in A[x_1, \dots, x_n]$, given by the codes of its coefficients. The instance is a yes-instance when there is $(r_1, \dots, r_n) \in R^n$ with

$$
f(r_1, \dots, r_n) = 0 .
$$

The problem is *decidable* (has a positive answer) when some Turing machine halts on every instance and accepts exactly the yes-instances; otherwise it is *undecidable* (has a negative answer). When $R$ is countable and carries such an encoding, *Hilbert's tenth problem over $R$* means the case $A = R$. Hilbert's original problem is the case $A = R = \mathbb{Z}$.

Conventions:

- The solutions are sought in $R$, which may be larger than $A$: for an uncountable $R$, such as a function field over an uncountable field of constants, only the coefficients are restricted to a countable subring.
- Two encodings of $A$ that a Turing machine can convert into each other give the same answer; the sources leave the encoding implicit for this reason.
- Instances are single equations. For a computable integral domain $R = A$ whose fraction field is not algebraically closed, a finite system of equations can be effectively replaced by one equation with the same solutions, so allowing systems does not change the answer.

## Depends on

None.

## Proof depends on

None.

## Expansion

The usual route to a negative answer over a ring $R \supseteq \mathbb{Z}$ is a Diophantine definition of $\mathbb{Z}$ over $R$: a polynomial $g(t, y_1, \dots, y_m)$ with coefficients in $A$ such that $t \in \mathbb{Z}$ exactly when $g(t, y) = 0$ for some $y \in R^m$. Given $f \in \mathbb{Z}[x_1, \dots, x_n]$, the equation $f(x) = 0$ together with $g(x_i, y^{(i)}) = 0$ for each $i$ has a solution in $R$ exactly when $f$ has an integer zero, and combining the system into one equation reduces Hilbert's original problem to the problem over $R$. Over fields of positive characteristic, where $\mathbb{Z}$ is not a subset, one instead interprets the integers with addition and a divisibility relation by existential formulas.

## Sources

- Bjorn Poonen, *Using elliptic curves of rank one towards the undecidability of Hilbert's tenth problem over rings of algebraic integers*, in: Algorithmic Number Theory (ANTS-V, Sydney, 2002), Lecture Notes in Computer Science 2369, Springer, 2002, pp. 33–42, https://doi.org/10.1007/3-540-45455-1_4; the version read is arXiv:math/0204001v1, the only arXiv version. The introduction defines Hilbert's tenth problem over a ring $R$ with a fixed encoding, and over an uncountable ring with a countable set of admissible polynomials.
- Kirsten Eisenträger (Eisentraeger) and Alexandra Shlapentokh, *Hilbert's tenth problem over function fields of positive characteristic not containing the algebraic closure of a finite field*, J. Eur. Math. Soc. 19 (2017), no. 7, 2103–2138, https://doi.org/10.4171/JEMS/714. The introduction of arXiv:1306.2669v1 defines recursive rings and records that a system of equations over a recursive integral domain whose fraction field is not algebraically closed can be replaced by one equation.
- Jochen Koenigsmann, *Undecidability in number theory*, in: Model Theory in Algebra, Analysis and Arithmetic, Lecture Notes in Mathematics 2111, Springer, 2014, pp. 159–195, https://doi.org/10.1007/978-3-642-54936-6_5; Sections 3 and 5 of arXiv:1309.0441v1.
