# Shannon-type synthesis: every function has circuits of size 12·2^n/n + o(2^n/n)

Every Boolean function $f:\{0,1\}^n\to\{0,1\}$ has a circuit over the full binary basis $B_2$ of size at most $12\cdot 2^n/n+o(2^n/n)$; that is, $C(B_n)\le 12\cdot 2^n n^{-1}+o(2^n n^{-1})$, where $C(B_n)$ is the largest $B_2$-complexity of a function of $n$ variables.

## Proof sketch

By the Shannon expansion $f=(\neg x_n\wedge f_0)\vee(x_n\wedge f_1)$ a *decoding circuit* computes $f$ from its two subfunctions with three more gates. Compute first all $2^{2^k}$ functions of $k$ variables, with at most $3\cdot 2^{2^k}+6\cdot 2^{2^{k-1}}$ gates; the decoding circuit then stops after $n-k$ steps, using at most $3\cdot 2^{n-k}-3$ further gates. So $C(B_n)\le 3(2^{n-k}+2^{2^k})+6\cdot 2^{2^{k-1}}$ for every $k$, and $k=\lfloor\log_2 n\rfloor-1$ gives the bound. Derived here for De Morgan circuits with all gates charged: split the inputs into $a=\lfloor\log_2 n\rfloor-1$ address bits $x$ and $m=n-a$ data bits $y$, so $n/4<2^a\le n/2$ and $2^m<4\cdot 2^n/n$, and write $f=\bigvee_b [y=b]\wedge f_b(x)$. The minterms of $y$ cost at most $4\cdot 2^m<16\cdot 2^n/n$ gates; all $2^{2^a}\le 2^{n/2}$ functions of $x$ cost at most $2^{2^a}+2n+1$ gates (each nonzero function is one OR of a smaller one with a minterm); the $2^m$ ANDs and $2^m-1$ ORs cost fewer than $8\cdot 2^n/n$. The total is below $24\cdot 2^n/n+2^{n/2}+2n+1\le 27\cdot 2^n/n$ for every $n\ge 16$.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [All minterms in linear size](all-minterms-in-linear-size.md)
- [Shannon expansion](../../../../../Logic/propositional-logic/functional-completeness/shannon.md)

## Sources

- Claude E. Shannon, "The Synthesis of Two-Terminal Switching Circuits", Bell System Technical Journal 28(1), 59–98, 1949.
- Oleg B. Lupanov, "On a Method of Circuit Synthesis", Izvestiya Vysshikh Uchebnykh Zavedenii. Radiofizika 1(1), 120–140, 1958.
- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987 (Chapter 4, Section 2, equations (2.5)–(2.11), pp. 90–91).
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
