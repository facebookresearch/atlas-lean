# Savitch's theorem: NSPACE(s) ⊆ DSPACE(s²)

For every $s:\mathbb{N}\to\mathbb{N}$ with $\log_2 n\le s(n)$,

$$
\mathsf{NSPACE}(s(n))\subseteq\mathsf{DSPACE}\bigl(s(n)^2\bigr).
$$

No constructibility assumption on $s$ is required; the nondeterministic machine is only required to respect the space bound along every computation prefix (its branches need not halt), and the deterministic simulator halts on every input. In particular $\mathsf{NL}\subseteq\mathsf{DSPACE}(\log^2 n)$.

## Proof sketch

Decide reachability from the initial to an accepting configuration in the configuration graph with $N=2^{O(s)}$ vertices by the recursive midpoint test $\mathrm{Reach}(u,v,2^k)\iff\exists w\,[\mathrm{Reach}(u,w,2^{k-1})\wedge\mathrm{Reach}(w,v,2^{k-1})]$, of depth $O(s)$ with frames of $O(s)$ bits. Without constructibility, run the search for increasing widths $w=1,2,\dots$ and stop at the first width for which no configuration of width $w+1$ is reachable.

## Depends on

- [Nondeterministic space classes](../../../time-and-space-complexity-classes/nspace.md)
- [Deterministic space classes on multi-tape machines](../../../time-and-space-classes-on-multi-tape-machines/dspace.md)

## Proof depends on

- [Configuration graph of a space-bounded machine](../../configuration-graph-of-a-space-bounded-machine.md)
- [Savitch's theorem: NPSPACE = PSPACE](../../../savitch.md)

## Sources

- Walter J. Savitch, "Relationships between Nondeterministic and Deterministic Tape Complexities", Journal of Computer and System Sciences 4(2), 1970.
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013, Theorem 8.5 (stated there for $f(n)\ge n$).
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
