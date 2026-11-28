# Universality of a state of a multi-tape automaton is undecidable

No algorithm decides whether every configuration is accepted from a given state of a given multi-tape automaton, already for
two-tape automata with three states.

**Theorem.** Given a $d$-tape automaton $\mathcal{M}$ and a state $q$ of $\mathcal{M}$, in the sense of
[multi-tape automata on infinite words](multi-tape-automata-on-infinite-words.md), it is undecidable whether $q$ is universal.
The problem remains undecidable when restricted to $2$-tape automata with $3$ states.

In the restricted version $d = 2$ and the number of states is $3$, but the alphabets and the transitions are part of the input.
With the associated graph-directed iterated function systems, the source turns this into the undecidability of whether a
self-affine attractor equals $[0, 1]^d$.

## Depends on

- [Multi-tape automata on infinite words](multi-tape-automata-on-infinite-words.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof reduces the *prefix Post correspondence problem*: given pairs of nonempty words $(u_1, v_1), \dots, (u_n, v_n)$, are
there index words $i_1 \cdots i_m$ and $i_1 \cdots i_{m'}$, one a prefix of the other, with
$u_{i_1} \cdots u_{i_m} = v_{i_1} \cdots v_{i_{m'}}$? It is undecidable by a reduction from the Post correspondence problem that
interleaves new separator symbols. From an instance over an alphabet
$\mathcal{B}$ one builds a $2$-tape automaton with states $X, U, V$, first tape over the indices $\{1, \dots, n\}$ and second tape
over $\mathcal{B} \cup \{\#\}$: from $X$ and from $U$ it reads $i \mid u_i$ into $U$, from $X$ and from $V$ it reads $i \mid v_i$ into
$V$, and further transitions loop at $X$, or return from $U$ or $V$ to $X$, on short words that disagree with $u_i$ or $v_i$.
If the instance has a solution with $u_{i_1} \cdots u_{i_m} = v_{i_1} \cdots v_{i_{m'}}$, then every configuration starting with
$i_1 \cdots i_m \mid u_{i_1} \cdots u_{i_m} \#$ forces the automaton into $U$ or $V$ and blocks it at the symbol $\#$, so $X$ is not
universal. If there is no solution, a strategy that avoids entering $U$ or $V$ when this would lead to such a block always finds
a move, so every configuration is $X$-accepted.

## Sources

- T. Jolivet and J. Kari, "Undecidable properties of self-affine sets and multi-tape automata", in *Mathematical Foundations of Computer Science 2014*, Lecture Notes in Computer Science 8634, pp. 352–364, Springer, 2014, doi:10.1007/978-3-662-44522-8_30; numbering of the version arXiv:1401.0705v2: Theorem 2.5 with its proof, Lemma 2.3 (prefix Post correspondence problem) and Theorem 4.1 (attractors equal to the unit cube).
