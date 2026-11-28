# Solving recursive Büchi games is hard for Boolean combinations of Σ¹₁ sets

Deciding whether player 0 wins a Büchi game played on a decidable infinite graph is at least as hard as every Boolean combination of $\Sigma^1_1$ problems, so it lies far beyond the arithmetical hierarchy.

**Theorem (Hutagalung, Hundeshagen, Kuske, Lange and Lozes).** A *recursive Büchi game* is a graph $G = (V, E, \mathrm{Own}, \mathrm{Fin}, v_I)$ in which $V$ is a decidable set of nodes, $\mathrm{Own}, \mathrm{Fin} \subseteq V$ are decidable, $E \subseteq V \times V$ is a decidable set of edges and $v_I$ is the starting node. A play starts at $v_0 = v_I$; at a node $v_i \in \mathrm{Own}$ player 0 chooses an edge $(v_i, v_{i+1}) \in E$, at any other node player 1 does. A player who cannot choose a successor loses, and player 0 wins an infinite play $v_0 v_1 \cdots$ if $v_i \in \mathrm{Fin}$ for infinitely many $i$. The *recursive Büchi game problem* asks, given such a game represented by Turing machines, whether player 0 has a winning strategy; the input consists of the starting node $v_I$ and Turing machines that halt on every input and decide $V$, $\mathrm{Own}$, $\mathrm{Fin}$ (as sets of binary strings) and $E$ (as a set of pairs of them), so the problem is a promise problem on such machines. This problem is hard for the class $B\Sigma^1_1$ of all Boolean combinations of problems from $\Sigma^1_1$ (see [analytical hierarchy](../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)).

The existence of a winning strategy is a $\Sigma^1_2$ statement and, by Borel determinacy, also a $\Pi^1_2$ statement, so the problem lies in $\Sigma^1_2 \cap \Pi^1_2$, a class without complete problems. The source reduces this problem to multi-buffer simulation between Büchi automata over the trace alphabet $(\{a, b\}, \{c\})$ with one unbounded buffer and one buffer of capacity $0$, which is therefore $B\Sigma^1_1$-hard (Corollary 11), whereas buffered simulation with a single unbounded buffer is decidable in exponential time.

## Depends on

- [Analytical hierarchy](../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof starts from Kleene's theorem that the set of (codes of) recursive trees with an infinite branch is $\Sigma^1_1$-hard, so that the set of tuples $(S_i, T_i)_{1 \le i \le n}$ of recursive trees such that, for some $i$, $S_i$ has an infinite branch while $T_i$ does not, is complete for $B\Sigma^1_1$. For a tree $S_i$, add a node $g_i$ with edges from every node (including $g_i$) to $g_i$, give all nodes to player 0, subdivide every edge into a path of length $2$, and let $\mathrm{Fin}$ be the original nodes: player 0 wins from the root iff $S_i$ has an infinite branch, since a play that escapes to $g_i$ visits $\mathrm{Fin}$ only finitely often. For $T_i$ the construction is dual, with the new node $h_i$ and its loop as the only winning nodes, so that player 0 wins iff $T_i$ has no infinite branch. For each $i$ the direct product of the two games is won by player 0 iff $S_i$ has an infinite branch and $T_i$ does not, since a play in the first component cannot leave the winning nodes once it enters them. Finally a new start node of player 0 with edges to the starts of all these products lets player 0 choose $i$, so player 0 wins iff some $i$ has this property.

## Sources

- M. Hutagalung, N. Hundeshagen, D. Kuske, M. Lange and É. Lozes, "Multi-Buffer Simulations for Trace Language Inclusion", in *Proceedings of the International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2016)*, Electronic Proceedings in Theoretical Computer Science 226, 2016, pp. 213–227, doi:[10.4204/EPTCS.226.15](https://doi.org/10.4204/EPTCS.226.15); read as arXiv:1609.04098v1, whose numbering is used here: Section 4 (definition of recursive Büchi games and their membership in $\Sigma^1_2 \cap \Pi^1_2$, Theorem 6 with its proof, Theorem 9 and Corollary 11).
