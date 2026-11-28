# Universality of two-way nondeterministic two-dimensional automata is undecidable

For nondeterministic automata reading a rectangular array of symbols with a head that may only move down or right, no algorithm decides whether every array is accepted, nor whether two such automata are equivalent; equivalence is decidable for the deterministic version.

A *two-dimensional word* is a finite rectangular array of symbols from a finite alphabet $\Sigma$, surrounded by a boundary symbol $\#$. A *two-dimensional automaton* $(Q,\Sigma,\delta,q_0,q_{\mathrm{accept}})$ has a finite set of states and a head starting in the upper-left corner; the transition function maps a state and the symbol under the head to a new state and a move up, down, left or right, and the automaton accepts by entering $q_{\mathrm{accept}}$; it is nondeterministic if $\delta$ maps to sets of such pairs. In a *two-way* two-dimensional automaton the head moves only down or right, so it reads each symbol at most once; in a *three-way* one it moves down, left or right.

**Theorem (Smith and Salomaa).** The universality problem for two-way nondeterministic two-dimensional automata is undecidable (Theorem 10 of arXiv:1904.11100v1).

Hence their equivalence problem is undecidable as well (Corollary 11 of arXiv:1904.11100v1).

By contrast, equivalence (and inclusion) of two-way deterministic two-dimensional automata over a general alphabet is decidable, emptiness of two-way nondeterministic two-dimensional automata is in P, and emptiness of unary three-way nondeterministic ones is NP-complete.

## Depends on

- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Emptiness of a linear bounded automaton on computable input slices is undecidable](../../undecidable-problems/emptiness-problem-for-linear-bounded-automata/exists-is-lba-not-computable-pred-forall.md)

## Expansion

The reduction is from emptiness of deterministic linear bounded automata. Given such an automaton $\mathcal M$, a two-way nondeterministic two-dimensional automaton reads arrays whose rows are double encodings of configurations of $\mathcal M$ and accepts exactly the arrays that are not accepting computation tables: it nondeterministically checks that some row is not a configuration, that the first row is not initial or the last not final, or that some row does not follow from the previous one, a changed symbol being checked by a downward move in its column, and the double encoding letting a down-and-right head check leftward moves of $\mathcal M$. So it accepts every array iff $L(\mathcal M)=\emptyset$.

## Sources

- Taylor J. Smith and Kai Salomaa, "Decision Problems for Restricted Variants of Two-Dimensional Automata", in *Implementation and Application of Automata (CIAA 2019)*, Lecture Notes in Computer Science 11601, 2019, pp. 222–234, doi:[10.1007/978-3-030-23679-3_18](https://doi.org/10.1007/978-3-030-23679-3_18); read in arXiv:1904.11100v1 ([arXiv](https://arxiv.org/abs/1904.11100v1)), whose numbering is used: Section 2 (Definitions 1–3), Section 4 (Theorem 8 on equivalence of deterministic two-way automata, Theorem 10 and Corollary 11) and Section 3 (emptiness).
