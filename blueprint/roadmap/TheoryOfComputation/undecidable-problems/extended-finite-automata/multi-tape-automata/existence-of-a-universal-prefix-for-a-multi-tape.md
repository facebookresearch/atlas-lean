# Existence of a universal prefix for a multi-tape automaton is undecidable

No algorithm decides whether a given state of a given multi-tape automaton has a universal prefix, already for two-tape automata
with three states.

**Theorem.** Given a $d$-tape automaton $\mathcal{M}$ and a state $q$ of $\mathcal{M}$, in the sense of
[multi-tape automata on infinite words](multi-tape-automata-on-infinite-words.md), it is undecidable whether $q$ admits a
universal prefix, that is, a finite word $x$ such that $xy$ is $q$-accepted for every infinite configuration $y$. The problem
remains undecidable when restricted to $2$-tape automata with $3$ states.

The source also records that, given a $2$-tape automaton with $3$ states and two states $q, r$, it is undecidable whether $q$
and $r$ have a common universal prefix. Through the associated graph-directed iterated function systems this gives the
undecidability of whether a self-affine attractor has empty interior.

## Depends on

- [Multi-tape automata on infinite words](multi-tape-automata-on-infinite-words.md)

## Proof depends on

- [Universality of a state of a multi-tape automaton is undecidable](universality-of-a-state-of-a-multi-tape-automato.md)

## Expansion

The proof modifies the reduction from the prefix Post correspondence problem used for universality: a new symbol is inserted
after each letter of each word $u_i$ and $v_i$, and the transitions back to the start state are adjusted, so that in the
resulting automaton the start state has a universal prefix if and only if it is universal, which happens exactly when the
instance has no solution.

## Sources

- T. Jolivet and J. Kari, "Undecidable properties of self-affine sets and multi-tape automata", in *Mathematical Foundations of Computer Science 2014*, Lecture Notes in Computer Science 8634, pp. 352–364, Springer, 2014, doi:10.1007/978-3-662-44522-8_30; numbering of the version arXiv:1401.0705v2: Theorem 2.6 with its proof, Remark 2.7 (common universal prefixes) and Theorem 4.2 (attractors with empty interior).
