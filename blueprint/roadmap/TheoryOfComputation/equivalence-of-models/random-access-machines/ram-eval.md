# Output of a RAM machine

Let $P$ be a program of length $\ell$ and $x_0, \dots, x_{k-1}$
inputs. Run $P$ from the initial state on these inputs. If for some $t$ the program counter
after $t$ steps is at least $\ell$, the output of $P$ on these inputs is the accumulator after
the least such number of steps; otherwise the output is undefined.

## Sources

- Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2.
