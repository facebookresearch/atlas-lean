# Configuration graph of a space-bounded machine

Let $M$ be a deterministic or nondeterministic Turing machine with a read-only input tape and work tapes, all of whose computation branches halt, and let
$S(n) \ge \log n$ be a space bound for $M$. A *configuration* of $M$ consists of its state, its head positions and the contents of its non-blank work-tape
cells. For an input $x$, the *configuration graph* $G_{M,x}$ is the directed graph whose vertices are all configurations of $M$ on inputs of length $|x|$ that use at most $S(|x|)$ work-tape cells, with an edge from $C$ to $C'$ when $C'$ is reached from $C$ in one step of the transition function; it has out-degree at most one if $M$ is
deterministic, with out-degree $0$ exactly at halting configurations, and out-degree at most the branching bound of the transition relation, a constant depending on $M$, if $M$ is nondeterministic.

- After modifying $M$ to erase its work tapes and move all of its heads to the leftmost cell before entering its accepting state, there is a single accepting configuration $C_{\mathrm{accept}}$, and $M$ accepts $x$ if and only if
  $G_{M,x}$ has a directed path from $C^x_{\mathrm{start}}$ to $C_{\mathrm{accept}}$.
- If $M$ uses space $S(n)$, every vertex of $G_{M,x}$ is described by $c\,S(n)$ bits for a constant $c$ depending on $M$, so $G_{M,x}$ has at most $2^{c S(n)}$
  vertices, and given $x$, whether two strings of $c\,S(n)$ bits encode configurations $C$ and $C'$ with an edge from $C$ to $C'$ can be decided in space $O(S(n))$, by reading the input symbol under the input head of $C$ and checking one application of the transition function.

## Depends on

- [Nondeterministic decision in bounded time](../time-and-space-complexity-classes/ntmdecides-in-time.md)

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, <https://theory.cs.princeton.edu/complexity/>: Definition 4.1 and Remark 4.2 (space-bounded computation), Section 4.1 (configuration graphs, Figure 4.2) and Claim 4.4.
