# Post's theorem: simple sets exist

Let $W_e$ be the $e$-th recursively enumerable set and $W_{e,s}$ its finite approximation at stage $s$. A set $A \subseteq \mathbb{N}$ is *simple* if $A$ is recursively
enumerable, its complement is infinite, and its complement contains no infinite recursively enumerable set.

**Theorem (Post).** There is a simple set.

The set $A = \bigcup_s A_s$ is built in stages: $A_0 = \emptyset$, and at stage $s + 1$ the least $e < s$ with $W_{e,s} \cap A_s = \emptyset$ and some $x > 2e$ in $W_{e,s}$ acts by adding the least
such $x$. Each $e$ acts at most once, so every infinite $W_e$ meets $A$, and $|A \cap \{0, \dots, 2e-1\}| \le e$, so the complement of $A$ is infinite. A simple set is not
recursive, since otherwise its complement would be an infinite recursively enumerable set disjoint from it.

## Sources

- A. Miller, *Lecture notes in Recursion Theory*, University of Wisconsin, 2008, <https://people.math.wisc.edu/~awmille1/old/m773-07/recthy.pdf>: Section 15, Definition 15.1 and Theorem 15.2 (Post) with its proof.
