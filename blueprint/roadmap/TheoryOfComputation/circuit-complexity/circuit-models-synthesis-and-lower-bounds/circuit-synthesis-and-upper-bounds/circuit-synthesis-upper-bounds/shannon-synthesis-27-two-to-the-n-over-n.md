# Shannon-type synthesis: every function has circuits of size 27·2^n/n

For every $n\ge 16$, every Boolean function $f:\{0,1\}^n\to\{0,1\}$ has a De Morgan circuit (all gates charged) of size at most $27\cdot 2^n/n$.

## Proof sketch

Split the inputs into $a=\lfloor\log_2 n\rfloor-1$ address bits and $n-a$ data bits. Compute all minterms of both blocks and all $2^{2^a}$ functions of the address block (a shared column library of size $O(2^{2^a})$). For each assignment of the data bits select the column of the truth table it determines, and combine by a disjunction over data minterms; the total is $O(2^n/n)$ with the constant $27$.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [All minterms in linear size](all-minterms-in-linear-size.md)
- [Shannon expansion](../../../../../Logic/propositional-logic/functional-completeness/shannon.md)

## Sources

- Claude E. Shannon, "The Synthesis of Two-Terminal Switching Circuits", Bell System Technical Journal, 1949.
- Oleg B. Lupanov, "On a Method of Circuit Synthesis", Izvestiya Vysshikh Uchebnykh Zavedenii. Radiofizika, 1958.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
