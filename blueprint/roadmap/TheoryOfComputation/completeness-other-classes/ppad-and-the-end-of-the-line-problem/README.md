# PPAD and the END-OF-THE-LINE problem

Problems such as finding a Nash equilibrium or a Brouwer fixed point always have a solution, so NP-completeness is the wrong yardstick for them: a reduction from SAT would give NP = coNP (Papadimitriou, *Algorithmic Game Theory*, Section 2.2). Papadimitriou (1994) classified such total search problems by the combinatorial lemma that proves their totality. PPAD ("polynomial parity argument, directed version") rests on the lemma that a directed graph with in- and out-degrees at most one that has a source has a sink. Daskalakis, Goldberg and Papadimitriou (SIAM J. Comput. 2009) define PPAD as the total search problems polynomial-time reducible to END-OF-THE-LINE: given circuits $S$ and $P$ on $\{0,1\}^n$ with $P(0^n) = 0^n \neq S(0^n)$, find $x$ with $P(S(x)) \neq x$ or $S(P(x)) \neq x \neq 0^n$.

The pages below treat the combinatorial principle for arbitrary finite graphs presented by maps $S$ and $P$, rather than by circuits; PPAD itself is a class of total search problems, not of decision problems like the classes of [P, NP and coNP](../../complexity-classes/the-classes-p-np-and-conp/README.md). The main results of the theory, as stated in that paper (there r-Nash asks for an approximately well-supported $1/A$-Nash equilibrium of an r-player game in normal form, $A$ part of the input), are:

- r-Nash is in PPAD for every number of players $r \geq 2$;
- the problem BROUWER, a discretised three-dimensional Brouwer problem, is PPAD-complete;
- 3-Nash is PPAD-complete, and so is 2-Nash, by Chen and Deng (the same paper gives a short proof).

Insisting on a sink rather than "a sink or another source" gives the class PPADS (same paper), even though a sink always exists ([Every END-OF-THE-LINE instance has a sink](exists-sink.md)).

- [The END-OF-THE-LINE graph](adj.md)
- [Out-degree at most one](out-unique.md)
- [In-degree at most one](in-unique.md)
- [Sinks of the END-OF-THE-LINE graph](forall-not-adj-iff.md)
- [Sources of the END-OF-THE-LINE graph](forall-not-adj-to-iff.md)
- [END-OF-THE-LINE is total](exists-solution.md)
- [Every END-OF-THE-LINE instance has a sink](exists-sink.md)

## Related topics

- [Nash's theorem](../../../GameTheory/noncooperative-games/nash-s-theorem/README.md): the total search problem whose complexity PPAD was designed to capture.
- [Bimatrix games and the Lemke–Howson algorithm](../../../GameTheory/noncooperative-games/bimatrix-games-and-the-lemke-howson-algorithm/README.md): the path-following argument behind the definition of PPAD.
- [Brouwer fixed-point theorem](../../../Topology/algebraic-topology/brouwer-fixed-point-theorem/README.md): approximate Brouwer fixed points are PPAD-complete (BROUWER; Daskalakis, Goldberg and Papadimitriou).
- [Sperner's lemma](../../../Combinatorics/polytopes-simplicial-complexes/sperner-s-lemma/README.md): a door-counting parity argument of exactly the END-OF-THE-LINE kind.
- [Correlated equilibria](../../../GameTheory/noncooperative-games/correlated-equilibria/README.md): by contrast, a correlated equilibrium can be found in polynomial time in many succinctly represented games (Papadimitriou, *Algorithmic Game Theory*, Theorem 2.6).
- [NP-completeness](../../np-completeness/README.md): the notion that does not fit total search problems unless NP = coNP.
- [Boolean circuit complexity](../../circuit-complexity/README.md): END-OF-THE-LINE instances are presented by Boolean circuits.
