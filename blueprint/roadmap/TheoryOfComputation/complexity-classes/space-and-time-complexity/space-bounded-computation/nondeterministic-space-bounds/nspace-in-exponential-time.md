# Nondeterministic space s is within deterministic time 2^{O(s)}

For every $s$ with $\log_2 n\le s(n)$,

$$
\mathsf{NSPACE}(s)\subseteq\bigcup_{c}\mathsf{DTIME}\bigl(2^{c\,s(n)}\bigr),
$$

and for arbitrary $s$ the bound is $2^{O(\log n+s(n))}$. This holds for nondeterministic recognizers whose branches need not halt, and requires no constructibility of $s$.

## Proof sketch

Breadth-first search of the configuration graph, which has $2^{O(\log n+s(n))}$ vertices reachable from the start, decides whether an accepting configuration is reachable.

## Depends on

- [Nondeterministic space classes](../../../time-and-space-complexity-classes/nspace.md)
- [Deterministic time classes on multi-tape machines](../../../time-and-space-classes-on-multi-tape-machines/dtime.md)

## Proof depends on

- [Configuration graph of a space-bounded machine](../../configuration-graph-of-a-space-bounded-machine.md)
- [Exponential time bound from a space bound and halting](../../../containments-between-time-and-space-classes/runs-in-time-exponential-of-space.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
