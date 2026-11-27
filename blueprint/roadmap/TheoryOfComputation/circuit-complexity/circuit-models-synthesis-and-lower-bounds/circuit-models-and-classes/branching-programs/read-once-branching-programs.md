# Read-once (oblivious layered) branching programs

A **read-once branching program** of length $T$ and width $w$ with state set $[w]$ is given by a sequence of transition functions $\delta_t:[w]\times\{0,1\}^{b}\to[w]$, $t=1,\dots,T$, reading the input in consecutive blocks $y_1,\dots,y_T\in\{0,1\}^{b}$, each exactly once and in order, together with a start state and a set of accepting final states. It accepts $y$ if $\delta_T(\cdots\delta_1(q_0,y_1)\cdots,y_T)$ is accepting. Such a program is a program over the monoid of self-maps of $[w]$ and also an ordinary branching program of size $O(Tw\,2^{b})$. For $b=1$ this is the read-once branching program of [Read-once branching program and space-bounded pseudorandom generator](../../../../pseudorandomness-and-one-way-functions/space-bounded-and-small-bias-generators/read-once-branching-programs-and-space-bounded-prgs.md). A probabilistic machine of space $s(n)\ge\log_2 n$ reading its coins once corresponds, for each input, to a read-once program of width $2^{O(s)}$ on its coin sequence.

## Depends on

- [Deterministic and nondeterministic branching programs](branching-programs.md)
- [Read-once branching program and space-bounded pseudorandom generator](../../../../pseudorandomness-and-one-way-functions/space-bounded-and-small-bias-generators/read-once-branching-programs-and-space-bounded-prgs.md)
- [Programs over a monoid and bounded-width branching programs](monoid-programs.md)

## Sources

- Noam Nisan, "Pseudorandom Generators for Space-Bounded Computation", Combinatorica 12(4), 449–461, 1992.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
