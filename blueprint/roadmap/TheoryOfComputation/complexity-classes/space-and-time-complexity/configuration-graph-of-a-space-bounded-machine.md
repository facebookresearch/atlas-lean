# Configuration graph of a space-bounded machine

Let $M$ be a (possibly nondeterministic) Turing machine with a read-only input tape and work tapes, using space $s(n) \ge \log n$ on inputs of length $n$. For an input $x$ the *configuration graph* $G_{M,x}$ has as vertices the configurations of $M$ on $x$ that use at most $s(|x|)$ work cells (state, input-head position, work-head positions and work-tape contents) and an edge from $C$ to $C'$ when $M$ can move from $C$ to $C'$ in one step. It has at most $2^{c \cdot s(|x|)}$ vertices for a constant $c$ depending on $M$, whether $(C, C')$ is an edge can be decided in space $O(s(|x|))$, and $M$ accepts $x$ exactly when an accepting configuration is reachable from the start configuration.

## Depends on

- [Nondeterministic decision in bounded time](../time-and-space-complexity-classes/ntmdecides-in-time.md)
- [Reachability in a labelled transition system is transitive](../../../ComputerScience/process-calculi/labelled-transition-systems/trans.md)

## Expansion

This page becomes ready once:

- Configurations of a Turing machine with a read-only input tape and work tapes, with their one-step relation (statement prerequisite; not yet stated)
- A machine with k work tapes, state set Q and tape alphabet Γ has at most |Q| s^k |Γ|^{k s} configurations using s work cells on inputs of length n (proof prerequisite; not yet stated)
- Acceptance as reachability of an accepting configuration must be proved for possibly nonhalting nondeterministic machines

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009
- M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage Learning, 2013
