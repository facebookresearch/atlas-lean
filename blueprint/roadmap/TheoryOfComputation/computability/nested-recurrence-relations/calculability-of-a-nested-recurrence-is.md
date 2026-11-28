# Calculability of a nested recurrence relation is undecidable

For one explicit nested recurrence built from addition, subtraction and recursion only, no algorithm decides, given finitely many initial values, whether the recurrence then defines a value at every natural number.

**Definitions.** Let a sequence $A$ be given by finitely many *initial conditions*, prescribed values $A(n)$ for finitely many $n$, together with a recurrence for the other arguments. The sequence is *calculable* if for every $n \ge 0$ either $A(n)$ is an initial condition, or the calculation of $A(n)$ by the recurrence invokes $A$ only on arguments in $\{0, 1, \dots, n - 1\}$ (all of them calculable in turn). For example, Hofstadter's sequence $Q(n) = Q(n - Q(n-1)) + Q(n - Q(n-2))$ with $Q(1) = Q(2) = 1$ is not known to be calculable.

**Theorem (Celaya and Ruskey).** For the nested recurrence

$$
A(n) = A\bigl(n - 4 - A(A(n-4))\bigr) + 4A\bigl(A(n-2)\bigr) + A\bigl(2A(n - 4 - A(n-2)) + A(n-4)\bigr),
$$

there is no algorithm that decides, given a finite set of initial conditions for $A$, whether $A$ is calculable.

The recurrence is fixed; only the initial conditions are the input, given as a finite list of pairs $(n, A(n))$ of natural numbers (the reduction uses only natural-number values; later values computed by the recurrence may be negative). Calculability can fail when an argument falls outside $\{0, \dots, n - 1\}$, for instance when it is negative.

## Depends on

- [Decidability by multi-stack machines](../decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Tag systems emulate Turing machines](../../equivalence-of-models/tag-systems/tag-systems-emulate-turing-machines.md)
- [Halting is undecidable](../halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof simulates Post 2-tag systems, whose halting problem is undecidable because tag systems emulate Turing machines. It first replaces a tag system by a *reverse tag system*, a variant that can be simulated by lookups into earlier values, with deletion numbers restricted to $\{0, 2\}$. A simpler recurrence

$$
B(n) = \begin{cases} B(n-2) + 2B(B(n-1)), & n \text{ even}, \\ B\bigl(2B(n - 2 - B(n-1)) + B(n-2)\bigr), & n \text{ odd}, \end{cases}
$$

with initial conditions that encode the productions and the initial word, computes successive words of the reverse tag system, and becomes non-calculable exactly when the simulated system halts. Finally, initial conditions for $A$ are chosen so that $A(c_0 + 4n + j)$ is $0$ for $j = 0, 2$, equals $B(c_0 + 2n + 1)$ for $j = 1$ and $2B(c_0 + 2n + 2)$ for $j = 3$, and $A$ is calculable if and only if $B$ is. A good expansion links the three steps of the source as pages: the simulation of a tag system by its reverse tag system (Theorem 1), the simulation of the reverse tag system by $B$ (Theorem 2), and the equivalence of the calculability of $A$ and $B$ (Theorem 3).

## Sources

- M. Celaya and F. Ruskey, "An undecidable nested recurrence relation", in *How the World Computes: Turing Centenary Conference and 8th Conference on Computability in Europe (CiE 2012)*, Lecture Notes in Computer Science 7318, Springer, 2012, pp. 107–117, doi:10.1007/978-3-642-30870-3_12; read as arXiv:1203.0586v1, <https://arxiv.org/abs/1203.0586v1>: the recurrence and the calculability problem in the abstract and in Section 6 ("Reducing $A$ to $B$"), Theorem 3 there ($A$ is calculable if and only if $B$ is), Theorem 2 ($B$ simulates a reverse tag system) and the concluding remarks, in the numbering of that version. The recurrence stated here is the one displayed and used in Section 6; the abstract of that version prints a variant with the arguments $n - 4$ and $n - 2$ exchanged in two places.
