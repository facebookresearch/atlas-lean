# Value of a RAM operand

In a RAM state with register contents $r$, an operand resolves to
a natural number: the immediate operand $n$ resolves to $n$ itself, the direct operand $n$ to
the contents $r(n)$ of register $n$, and the indirect operand $n$ to $r(r(n))$.

## Sources

- Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2.
