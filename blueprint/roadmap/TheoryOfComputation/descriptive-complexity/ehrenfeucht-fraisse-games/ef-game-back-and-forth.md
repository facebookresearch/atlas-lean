# Duplicator wins the EF game iff there is a back-and-forth system

For structures $\mathfrak{A}, \mathfrak{B}$ in a relational vocabulary with $k$-tuples $\bar a, \bar b$ and $n \in \mathbb{N}$, Duplicator has a winning strategy in the $n$-round Ehrenfeucht–Fraïssé game starting from the position $(\bar a, \bar b)$ if and only if $\bar a \mapsto \bar b$ belongs to the top level $I_n$ of some back-and-forth system $(I_j)_{j \le n}$ of depth $n$ between $\mathfrak{A}$ and $\mathfrak{B}$.

## Proof sketch

The levels of a back-and-forth system give Duplicator's answers: from a position in $I_{j+1}$, forth and back provide a reply landing in $I_j$, so $I_n$ is safe for $n$ further rounds. Conversely, (derived) the positions from which Duplicator wins with $j$ rounds left form $I_j$; this system is nested because the winning relation is monotone in the number of rounds, and (derived) it is invariant under isomorphisms and under permutations of the pebbled pairs.

## Depends on

- [Back-and-forth systems](back-and-forth-systems.md)
- [Ehrenfeucht–Fraïssé theorem](../finite-model-theory/ehrenfeuchtfraisse-theorem.md)

## Sources

- M. Otto, Model Theory, lecture slides, Technische Universität Darmstadt, Summer 2013, Section I.3 "Back&Forth", slides 26–28 (back-and-forth systems $(I_k)_{k \le m}$; $m$-isomorphy as membership in $I_m$ and as a winning strategy for the second player in the $m$-round game).
- A. Ehrenfeucht, "An Application of Games to the Completeness Problem for Formalized Theories", Fundamenta Mathematicae 49, 129–141, 1961.
- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
