# RAM-decidable predicate

A predicate $P$ on the natural numbers is RAM decidable when
there is a RAM program, a finite list of RAM instructions, such that for every natural number $n$
the program, started with $n$ in register $0$ and with the accumulator, the program counter and
every other register at $0$, halts (its program counter reaches or passes the end of the
program) with $1$ in the accumulator if $P(n)$ holds and with $0$ in the accumulator otherwise;
that is, its RAM evaluation on the single input $n$ equals the characteristic function of $P$
at $n$.

## Sources

- Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2.
