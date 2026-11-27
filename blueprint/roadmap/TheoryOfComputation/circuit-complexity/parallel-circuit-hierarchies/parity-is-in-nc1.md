# Parity is in NC1

For $n\ge1$, the parity of $n$ bits has a De Morgan formula of depth at most $2\lceil\log_2 n\rceil$ (negations free), namely a balanced tree of exclusive ors, each expanded as $(x\wedge\neg y)\vee(\neg x\wedge y)$. Hence $\mathrm{PARITY}\in\mathsf{NC}^1$ nonuniformly.

## Proof sketch

Each XOR level contributes two AND/OR levels and a balanced tree has $\lceil\log_2 n\rceil$ levels.

## Depends on

- [The AC, TC and AC[q] hierarchies](ac-tc-and-acq-hierarchies.md)
- [The parity language](../../complexity-classes/time-and-space-complexity-classes/parity-dec.md)

## Sources

- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
