# Alternating Turing machine

An **alternating Turing machine** is a nondeterministic multi-tape Turing machine $M$ with a read-only input tape, finitely many work tapes, a finite state set $Q$ partitioned into *existential* states $Q_\exists$, *universal* states $Q_\forall$, and halting states (accepting and rejecting), and a transition relation giving each non-halting configuration finitely many successor configurations.

Acceptance is the least fixed point of the following rules on configurations $C$: an accepting halting configuration is accepting; an existential configuration is accepting if **some** successor is accepting; a universal configuration is accepting if **every** successor is accepting (and it has at least one). $M$ accepts $x$ if its initial configuration on $x$ is accepting. Equivalently, acceptance is a win for the existential player in the two-player game whose positions are configurations, where the owner of the current state chooses the next move.

$M$ runs in time $t(n)$ if every computation path on every input of length $n$ halts within $t(n)$ steps, and in space $s(n)$ if every configuration reachable from the initial configuration on an input of length $n$ uses at most $s(n)$ work-tape cells.

## Depends on

- [Nondeterministic space classes](../../time-and-space-complexity-classes/nspace.md)
- [Nondeterministic time classes](../../time-and-space-complexity-classes/ntime.md)

## Sources

- Ashok K. Chandra, Dexter C. Kozen and Larry J. Stockmeyer, "Alternation", Journal of the ACM 28(1), 1981.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
