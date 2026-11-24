# Every END-OF-THE-LINE instance has a sink

Let $V$ be a finite set, let $S, P : V \to V$ be maps and let $o \in V$ satisfy $P(o) = o$ and
$S(o) \neq o$. Then some vertex $x$ has no outgoing edge in the
[END-OF-THE-LINE graph](adj.md) of $S$ and $P$, that is, $P(S(x)) \neq x$.

Proof: otherwise $P \circ S$ is the identity, so $S$ is injective, hence surjective on the finite
set $V$; writing $o = S(y)$ gives $y = P(S(y)) = P(o) = o$, so $S(o) = o$, a contradiction. This
is the parity lemma "a directed graph with in- and out-degrees at most one that has a source has
a sink" quoted in Daskalakis, Goldberg and Papadimitriou (2009).

## Informally uses

- [Sinks of the END-OF-THE-LINE graph](forall-not-adj-iff.md): a vertex without outgoing edge is one with $P(S(x)) \neq x$.

## Background

- As a search problem, asking for a sink only (rather than a sink or a nonstandard source) defines the class PPADS, apparently larger than PPAD (Daskalakis, Goldberg and Papadimitriou 2009); existence is not the issue there, finding one is.
- [Sperner's lemma in dimension two (parity form)](../../../Combinatorics/polytopes-simplicial-complexes/sperner-s-lemma/odd-card-rainbow.md): a parity argument of the same kind.
- [A nondegenerate bimatrix game has an odd number of Nash equilibria](../../../GameTheory/noncooperative-games/bimatrix-games-and-the-lemke-howson-algorithm/odd-ncard-is-bimatrix-nash.md): the Lemke–Howson instance of the principle.
