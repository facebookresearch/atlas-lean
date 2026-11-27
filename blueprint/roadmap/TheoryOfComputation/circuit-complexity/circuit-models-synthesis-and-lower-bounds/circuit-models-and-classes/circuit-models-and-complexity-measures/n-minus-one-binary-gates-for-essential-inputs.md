# A function depending on all inputs needs n - 1 binary gates

Let $f:\{0,1\}^n\to\{0,1\}$, $n\ge 1$, depend on all of its $n$ inputs. Then every circuit computing $f$ over a basis whose gates have fan-in at most two (for instance the De Morgan basis with free negations and constants) contains at least $n-1$ gates of fan-in two. More generally, if $r\ge 2$ bounds the fan-in, the number $s$ of gates of arity at least two satisfies $(r-1)s\ge n-1$.

## Proof sketch

Each input that $f$ depends on must be connected to the output. Gates of arity at most one do not merge paths, so the connected component of the output in the circuit graph is a tree-like structure in which every gate of arity $k$ merges at most $k$ components into one; starting from $n$ inputs, reaching one component requires merging $n-1$ times, and a gate of arity at most $r$ performs at most $r-1$ merges.

## Depends on

- [Straight-line programs and circuits over a basis](straight-line-program-over-a-basis.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
