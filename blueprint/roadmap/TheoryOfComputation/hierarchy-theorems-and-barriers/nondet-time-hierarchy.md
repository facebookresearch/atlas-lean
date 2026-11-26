# Nondeterministic time hierarchy

There is a language $L$ of bitstrings with $L \in \mathrm{NTIME}(n^2)$ and
$L \notin \mathrm{NTIME}(n)$: some nondeterministic multi-tape Turing machine decides $L$ in time
$c_1 n^2 + c_2$ for some constants $c_1, c_2$, and no nondeterministic multi-tape Turing machine
decides $L$ in time $c_1 n + c_2$ for any constants $c_1, c_2$.

This is the case of the time bounds $n$ and $n^2$ of the nondeterministic time hierarchy theorem.

## Background

- [Nondeterministic time classes](../complexity-classes/time-and-space-complexity-classes/ntime.md):
  the classes $\mathrm{NTIME}(t)$, with acceptance by a computation path that halts with output
  $1$.

## Sources

- S. A. Cook, "A hierarchy for nondeterministic time complexity", *Journal of Computer and System
  Sciences* 7 (1973), 343–353.
- S. Žák, "A Turing machine time hierarchy", *Theoretical Computer Science* 26 (1983), 327–333.
