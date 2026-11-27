# Recurring computations of two-counter machines are Σ¹₁-hard

A *nondeterministic two-counter machine* has two counters $C, D$ over $\mathbb{N}$ and instructions $1, \dots, n$, each of which increments or
decrements a counter and moves nondeterministically to one of two specified instructions, or jumps conditionally on a counter being
zero. A configuration is $(i, c, d)$; a *computation* is an infinite sequence of consecutive configurations starting at $(1, 0, 0)$, and
it is *recurring* if the instruction counter equals $1$ infinitely often. Deciding whether a given nondeterministic two-counter
machine has a recurring computation is $\Sigma^1_1$-hard, along the lines of the $\Sigma^1_1$-completeness of the existence of a computation of a
nondeterministic Turing machine on the empty tape that visits its starting state infinitely often.
In particular the problem is undecidable, and it is not even in the arithmetical hierarchy.

## Proof depends on

- [Two-counter machines are universal](two-counter-machines-are-universal.md)

## Expansion

This page becomes ready once:

- The $\Sigma^1_1$-completeness of the existence of a computation of a nondeterministic Turing machine on the empty tape that visits its starting state infinitely often (Harel, Pnueli and Stavi), from which the cited proof reduces (proof prerequisite; not yet stated)
- The analytical hierarchy, its level $\Sigma^1_1$ and the reductions that define hardness for it (statement prerequisite; not yet stated)

## Sources

- R. Alur and D. L. Dill, "A theory of timed automata", *Theoretical Computer Science* 126(2):183–235, 1994: Section 5.1, the definitions of nondeterministic two-counter machines and recurring computations and Lemma 5.1, which cites the Turing-machine result to D. Harel, A. Pnueli and J. Stavi, "Propositional dynamic logic of regular programs", *Journal of Computer and System Sciences* 26 (1983).
