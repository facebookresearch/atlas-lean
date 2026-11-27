# Myhill's characterization of creative sets

Let $W_e$ be the $e$-th recursively enumerable set and $K$ the halting set. A recursively enumerable set $A$ is *$m$-complete* (resp. *$1$-complete*) if $B \le_m A$
(resp. $B \le_1 A$) for every recursively enumerable $B$. A recursively enumerable set $C$ is *creative* if there is a recursive function $q$ such that for every $e$,
$W_e \cap C = \emptyset$ implies $q(e) \notin C \cup W_e$.

**Theorem (Myhill).** For a recursively enumerable set $C \subseteq \mathbb{N}$ the following are equivalent: $C$ is creative; $C \equiv_1 K$; $C$ is $1$-complete; $C$ is $m$-complete.

## Sources

- A. Miller, *Lecture notes in Recursion Theory*, University of Wisconsin, 2008, <https://people.math.wisc.edu/~awmille1/old/m773-07/recthy.pdf>: Section 14, Definitions 14.1 and 14.2 and Theorem 14.3 (Myhill) with its proof, and Section 11, Theorem 11.1 (Myhill's isomorphism theorem).
