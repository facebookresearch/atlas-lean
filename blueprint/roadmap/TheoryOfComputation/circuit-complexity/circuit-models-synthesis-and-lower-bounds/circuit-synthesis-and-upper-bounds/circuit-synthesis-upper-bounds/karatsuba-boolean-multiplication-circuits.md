# Karatsuba multiplication circuits

There is a constant $c$ such that for every $w\ge 1$ the full $2w$-bit product of two $w$-bit integers is computed by a De Morgan circuit with at most $c\,w^{\log_2 3}$ gates, every gate (including negations and constants) charged.

## Proof sketch

With $m=\lceil w/2\rceil$ and $a=a_0+2^m a_1$, $b=b_0+2^m b_1$, compute $a_0b_0$, $a_1b_1$ and $(a_0+a_1)(b_0+b_1)$ recursively. The middle sums have a carry bit; writing $a_0+a_1=r_a+2^m c_a$ reduces the third product to a recursive $m$-bit product plus masked additions of linear size. The recurrence $T(w)\le 3T(\lceil w/2\rceil)+O(w)$ gives $O(w^{\log_2 3})$.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)
- [Karatsuba multiplication](../../../../../ComputerScience/algebraic-and-numerical-algorithms/karatsuba-algorithm/karatsuba.md)

## Proof depends on

- [Ripple-carry adder](../../../ripple-carry-adder/ripple-carry-adder.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987, Theorem 3.2.2.
- Anatolii A. Karatsuba, Yuri P. Ofman, "Multiplication of Multidigit Numbers on Automata", Soviet Physics Doklady 7, 595–596, 1963.
