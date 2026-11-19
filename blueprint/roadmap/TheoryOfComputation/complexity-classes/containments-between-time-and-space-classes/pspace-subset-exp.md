# PSPACE is contained in EXP

$\mathrm{PSPACE} \subseteq \mathrm{EXP}$: every language of bitstrings decided by a deterministic
multi-tape Turing machine (with finitely many states) in polynomial space is decided by a
deterministic multi-tape Turing machine in time $O(2^{n^d})$ for some $d \in \mathbb{N}$.

The same machine works: a halting computation that uses polynomial space cannot repeat a
configuration, and there are exponentially many configurations of polynomial size.

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009, Chapter 4 (Space complexity).
