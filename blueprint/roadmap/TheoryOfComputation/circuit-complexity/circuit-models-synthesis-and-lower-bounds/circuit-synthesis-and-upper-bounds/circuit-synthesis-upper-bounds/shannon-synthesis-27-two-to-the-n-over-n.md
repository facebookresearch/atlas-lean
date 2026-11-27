# Shannon-type synthesis: every function has circuits of size 27·2^n/n

For every $n\ge 16$, every Boolean function $f:\{0,1\}^n\to\{0,1\}$ has a De Morgan circuit (all gates charged) of size at most $27\cdot 2^n/n$.

## Proof sketch

Split the inputs into $a=\lfloor\log_2 n\rfloor-1$ address bits $x$ and $m=n-a$ data bits $y$, so $n/4<2^a\le n/2$ and $2^m<4\cdot 2^n/n$. Write $f=\bigvee_b [y=b]\wedge f_b(x)$. The minterms of $y$ cost at most $4\cdot 2^m<16\cdot 2^n/n$ gates; all $2^{2^a}\le 2^{n/2}$ functions of $x$ are computed with at most $2^{2^a}+2n+1$ gates (each nonzero function is one OR of a smaller one with a minterm); the $2^m$ ANDs and $2^m-1$ ORs cost fewer than $8\cdot 2^n/n$. The total is below $24\cdot 2^n/n+2^{n/2}+2n+1\le 27\cdot 2^n/n$ for $n\ge 16$. The constant $27$ comes from this count; the sources give the $O(2^n/n)$ bound.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [All minterms in linear size](all-minterms-in-linear-size.md)
- [Shannon expansion](../../../../../Logic/propositional-logic/functional-completeness/shannon.md)

## Sources

- Claude E. Shannon, "The Synthesis of Two-Terminal Switching Circuits", Bell System Technical Journal 28(1), 59–98, 1949.
- Oleg B. Lupanov, "On a Method of Circuit Synthesis", Izvestiya Vysshikh Uchebnykh Zavedenii. Radiofizika 1(1), 120–140, 1958.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
