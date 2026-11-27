# Alternating time t is contained in deterministic space t

For every $t(n)\ge n$,

$$
\mathsf{ATIME}(t)\subseteq\mathsf{DSPACE}(t);
$$

more precisely $\mathsf{ATIME}(t)\subseteq\mathsf{DSPACE}(n+t(n))$ for every $t$.

## Proof sketch

Evaluate the game value of the alternating machine recursively along a depth-first traversal. Instead of storing configurations along the current path, store only the sequence of choices made (one bit per step) and recompute the current configuration from the initial one, so the space is $O(n+t(n))$.

## Depends on

- [Alternating time and space classes ATIME, ASPACE, AP, APSPACE and AL](alternating-time-and-space-classes.md)
- [Deterministic space classes on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/dspace.md)

## Sources

- Ashok K. Chandra, Dexter C. Kozen and Larry J. Stockmeyer, "Alternation", Journal of the ACM 28(1), 1981.
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
