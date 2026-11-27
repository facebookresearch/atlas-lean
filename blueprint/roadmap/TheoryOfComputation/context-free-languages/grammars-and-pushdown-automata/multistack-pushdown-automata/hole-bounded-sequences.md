# Holes and hole-bounded sequences

In a sequence of MPDA transitions, a push $\downarrow$ with matching pop $\uparrow$ is **closed by a well-nested continuation** if the factor $\downarrow w\uparrow$ is well-nested; such pushes never open holes. The remaining pushes are **hole pushes**. A **hole** of stack $i$ is a factor of the form $(\downarrow_i w)^{+}$: hole pushes on stack $i$, each followed by a well-nested sequence $w$ (which may use any stacks). At a position $x$, list the hole pushes pending at $x$ in order; two consecutive ones belong to the same open hole iff they push on the same stack and the factor between them is well-nested. The number of **open holes** at $x$ is the number of resulting groups, and a sequence is **$K$-hole-bounded** if at most $K$ holes are open at every position. Well-nested sequences are $0$-hole-bounded. The language of an MPDA restricted to a class of runs is the set of words with an accepting run in that class.

## Depends on

- [Well-nested sequences and matching of push/pop transitions](well-nested-transition-sequences.md)

## Sources

- S. Akshay, Paul Gastin, S. Krishna and Sparsa Roychowdhury, "Revisiting Underapproximate Reachability for Multipushdown Systems", Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2020), arXiv:2002.05950, 2020, Definition 1 (a hole of stack $i$ is a maximal factor $(\downarrow_i ws)^{+}$ with $ws$ well-nested; the hole-push formulation above makes precise which pushes are absorbed into well-nested factors, so that well-nested runs have no holes as in their Theorem 2).
