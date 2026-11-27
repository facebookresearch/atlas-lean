# Space-s computation yields branching programs of size 2^{O(s)}

Let $A\in\mathsf{DSPACE}(S)$ with $S(n)\ge\log_2 n$. There is a constant $c$ (depending on the machine) such that for every $n$ the restriction of $A$ to inputs of length $n$ is computed by a deterministic branching program of size at most $c^{\max(S(n),1)}$ over the $n$ input bits.

## Proof sketch

The nodes are the time-stamped configuration cores (state, input-head position, work-tape contents and head positions within the window of $S(n)$ cells) for steps $0,\dots,T$ with $T$ the configuration-count bound; a node queries the input bit under the input head and moves to the next core. Their number is $(T+1)(n+2)2^{O(S)}=2^{O(S)}$.

## Depends on

- [Deterministic and nondeterministic branching programs](branching-programs.md)
- [Deterministic space classes on multi-tape machines](../../../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dspace.md)

## Proof depends on

- [Configuration graph of a space-bounded machine](../../../../complexity-classes/space-and-time-complexity/configuration-graph-of-a-space-bounded-machine.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009 (web draft of 2007-01-08, Theorem 13.15).
