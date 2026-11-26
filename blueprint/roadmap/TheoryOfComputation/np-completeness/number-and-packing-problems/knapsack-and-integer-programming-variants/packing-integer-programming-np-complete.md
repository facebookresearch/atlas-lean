# PACKING INTEGER PROGRAMMING is NP-complete

The [decision problem](packing-integer-programming-dec.md) PACKING INTEGER PROGRAMMING belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Hardness comes from a special case: with a $0/1$ constraint matrix, right-hand side $b = 1$ and objective $c = 1$ the problem is SET PACKING.

## Sources

- P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem MAXIMUM PACKING INTEGER PROGRAMMING. The entry as printed allows fractional coordinates $x \in [0, 1]^n$, a linear program solvable in polynomial time; this page states the problem with binary coordinates $x \in \{0, 1\}^n$, as its name says. The two differ: with four unit-profit variables and $x_i + x_j \le 1$ for each pair, the fractional point with all coordinates $1/2$ has value $2$, while every binary solution has value at most $1$.
- A. Srinivasan, "Improved approximations of packing and covering problems", Proc. 27th Annual ACM Symposium on Theory of Computing (1995), 268-276, doi:10.1145/225058.225138.
- R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9 (SET PACKING is NP-complete).
