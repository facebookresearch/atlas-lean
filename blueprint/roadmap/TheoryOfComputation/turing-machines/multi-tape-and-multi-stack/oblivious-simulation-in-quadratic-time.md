# Oblivious simulation of a Turing machine in quadratic time

A Turing machine is *oblivious* if its head movement does not depend on the input beyond its length: for every input $x$ and every $i$, the position of each head at the $i$-th step of the computation on $x$ is a function of $|x|$ and $i$ only.

For every time-constructible $T : \mathbb{N} \to \mathbb{N}$ with $T(n) \ge n$, if $L \in \mathrm{DTIME}(T(n))$ then some oblivious Turing machine decides $L$ in time $O(T(n)^2)$.

## Proof sketch

Simulate the given machine on a single work tape that holds all its tapes on separate tracks. Each simulated step is one left-to-right and one right-to-left sweep over the first $O(T(n))$ cells, a length fixed in advance from $n$ through the time-constructibility of $T$, so every head position depends only on $|x|$ and the step number.

## Depends on

- [Deterministic time classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)

## Proof depends on

- [Deterministic time classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)
- [Decidability within time and space bounds in terms of machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/decidable-in-time-and-space-iff.md)

## Expansion

This page becomes ready once:

- Time-constructible functions (statement prerequisite; not yet stated)
- Simulation of a $k$-tape machine by a machine with one work tape holding the $k$ tapes on tracks, in time $O(T(n)^2)$ (proof prerequisite; not yet stated). The existing [quadratic overhead of the single-tape emulation](../../complexity-classes/quadratic-overhead-of-single-tape-simulation/exists-tm0-run-of-tm2-run.md) is for multi-stack machines and does not give oblivious head movement.

It is the proof prerequisite named in the expansion of [P is contained in P/poly](../../complexity-classes/time-and-space-complexity-classes/p-is-contained-in-p-poly.md).

## Sources

- Sanjeev Arora and Boaz Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, <https://theory.cs.princeton.edu/complexity/>: Claim 1.9 (quadratic simulation) and Remark 1.10 (making that simulation oblivious); Exercise 8 restates the quadratic bound. The additional two-tape refinement of that exercise is not part of this statement.
