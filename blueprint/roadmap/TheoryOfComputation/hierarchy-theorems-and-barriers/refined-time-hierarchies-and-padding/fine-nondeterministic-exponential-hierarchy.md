# Fine nondeterministic exponential-time hierarchy by lazy diagonalization

On binary words, for all reals $\delta>0$ and $c_0>0$,

$$
\mathsf{NTIME}\bigl(\lfloor 2^{\,n-c_0 n^{\delta}}\rfloor\bigr)\subsetneq\mathsf{NTIME}(2^{n}),
$$

and there is $k$ with $\mathsf{NTIME}(2^{n}/(n+1)^{k})\subsetneq\mathsf{NTIME}(2^{n})$.

## Proof sketch

Lazy diagonalization (Žák): on an interval of input lengths, mirror the simulated nondeterministic machine on the next length until the end of the interval, where the deterministic exponential simulation of the first length is affordable and is used to disagree. The universal simulation in time $O(t\log t)$ keeps the overhead to a polynomial factor in $n$.

## Depends on

- [Nondeterministic time classes](../../complexity-classes/time-and-space-complexity-classes/ntime.md)

## Proof depends on

- [Nondeterministic time hierarchy](../nondet-time-hierarchy.md)
- [Hennie–Stearns: a universal multi-tape machine with O(t log t) overhead](../../equivalence-of-models/ram-word-ram-and-pointer-machines/universal-simulation-t-log-t.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
- Stanislav Žák, "A Turing Machine Time Hierarchy", Theoretical Computer Science 26(3), 1983.
