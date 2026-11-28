# Oblivious simulation of a Turing machine in quadratic time

Use Arora and Barak's multitape model, with a read-only input tape, work tapes and an output tape. A machine in this model is *oblivious* if its head movement does not depend on the input beyond its length: for every input $x$ and every $i$, the position of each of its heads, the input and output heads as well as the work-tape heads, at the $i$-th step of the computation on $x$ is a function of $|x|$ and $i$ only.

For every time-constructible $T : \mathbb{N} \to \mathbb{N}$ (time-constructible functions satisfy $T(n) \ge n$), if a deterministic machine in this model decides a language $L$ within time $T(n)$, then an oblivious machine in the same model decides $L$ in time $O(T(n)^2)$.

## Proof sketch

Simulate the given machine on a single work tape that holds all its tapes on separate tracks. Each simulated step is one left-to-right and one right-to-left sweep over the first $O(T(n))$ cells, a length fixed in advance from $n$ through the time-constructibility of $T$, so the work-tape head position depends only on $|x|$ and the step number. The source asserts that, with some care, all head movements of the simulating machine are of this form, the input and output heads included (Remark 1.10); in the plain quadratic simulation the input and output tapes are still used as the simulated machine uses them, so that care is part of the construction.

## Depends on

The source's machine model and time-constructibility definitions are statement prerequisites still to be supplied, as listed below. The repository's time classes use a different tape model and are not substituted for them here.

## Proof depends on

The simulation and scheduling prerequisites are listed in the expansion below; the canonical time-class lemmas do not by themselves supply them.

## Expansion

This page becomes ready once:

- Time-constructible functions, including $T(n) \ge n$ (statement prerequisite; not yet stated)
- Model scoping: the source's machines have a read-only input tape, work tapes and an output tape, while [deterministic time classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md) uses CSLib's model with a separate read-only input tape, two-way infinite work tapes and a write-only output tape. Stating obliviousness for every head in that model, and relating the two models' time bounds, is part of the expansion (scoping obligation; not yet stated)
- The input and output head schedule that makes every head oblivious, not only the work-tape sweeps (proof prerequisite; not yet stated)
- Simulation of a $k$-tape machine by a machine with one work tape holding the $k$ tapes on tracks, in time $O(T(n)^2)$ (proof prerequisite; not yet stated). The existing [quadratic overhead of the single-tape emulation](../../complexity-classes/quadratic-overhead-of-single-tape-simulation/exists-tm0-run-of-tm2-run.md) is for multi-stack machines and does not give oblivious head movement.

This is the oblivious-simulation step used in the proof sketch of [P is contained in P/poly](../../complexity-classes/time-and-space-complexity-classes/p-is-contained-in-p-poly.md).

## Sources

- Sanjeev Arora and Boaz Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, <https://theory.cs.princeton.edu/complexity/>: Remark 1.5 (time-constructible functions, which satisfy $T(n) \ge n$), Claim 1.9 (simulation with one work tape plus input and output tapes in time $5kT(n)^2$) and Remark 1.10 (the head movements of the simulating machine can be made independent of the tape contents and dependent only on the input length); Exercise 8 defines obliviousness for each of the machine's heads and restates the quadratic bound. The additional two-tape refinement of that exercise is not part of this statement.
- CSLib, [`Configuration.lean` at commit `22b39634cb3dc80d829683ad1f65c5680b722309`](https://github.com/leanprover/cslib/blob/22b39634cb3dc80d829683ad1f65c5680b722309/Cslib/Computability/Machines/Turing/MultiTape/Configuration.lean): the module's model description and `Cfg` distinguish the read-only input, two-way work tapes and write-only output used in the scoping item above.
