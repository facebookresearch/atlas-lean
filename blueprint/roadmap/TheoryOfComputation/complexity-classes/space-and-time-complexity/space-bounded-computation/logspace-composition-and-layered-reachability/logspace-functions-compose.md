# Logarithmic-space computable functions compose

If $f$ and $g$ are computable by deterministic Turing machines with read-only input, write-only output and $O(\log n)$ work space, then so is $g\circ f$. Consequently logspace many-one reducibility is transitive, and $\mathsf{L}$ and $\mathsf{NL}$ are closed under logspace reductions.

## Proof sketch

Run the machine for $g$ on the virtual input $f(x)$: whenever it needs the $i$-th symbol of $f(x)$, rerun the machine for $f$ from the start, counting output symbols and discarding all but the $i$-th. Only the counter $i$ (of $O(\log|f(x)|)=O(\log n)$ bits) and the two work tapes are stored.

## Depends on

- [Log-space computable functions](../../../time-and-space-complexity-classes/log-space-computable.md)
- [Log-space many-one reductions](../../../time-and-space-complexity-classes/log-space-red.md)
- [Deterministic logarithmic space](../../../time-and-space-complexity-classes/log-space.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
