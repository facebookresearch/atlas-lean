# Team motion planning with reversible deterministic gadgets is RE-complete

Deciding whether a team has a forced win in a team motion-planning game, with unboundedly many moves and imperfect
information, is RE-complete already with copies of the locking 2-toggle, and with copies of any interacting-tunnel
reversible deterministic gadget.

**Theorem.** In the sense of [gadgets and motion-planning games](gadgets-and-motion-planning-games.md):

1. team motion planning with the locking 2-toggle gadget is RE-complete, and thus undecidable;
2. for every fixed interacting-$k$-tunnel reversible deterministic gadget, team motion planning with that gadget is
   RE-complete.

The input is a system of copies of the fixed gadget with initial states, the connection graph, the robots with their start
and goal locations and the partition into two teams; the construction uses three players, one black and two white. Membership
in RE holds for team motion planning with any set of gadgets. With perfect information and two players the problem with the
same gadgets is EXPTIME-complete instead.

## Depends on

- [Gadgets and motion-planning games](gadgets-and-motion-planning-games.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

None.

## Expansion

*Membership.* If the white team has a forced win, its winning strategy tree is finitely branching with finite branches, so by
König's lemma it is finite; enumerating finite strategies and checking each one recognizes the yes-instances.

*Hardness.* Reduce Team Private Constraint Logic, whose undecidability the source recalls from Hearn and Demaine and from which it derives RE-completeness, ultimately by
reduction from acceptance of a Turing machine on the empty input. Each player gets a region with an edge-selection area, a
path to the constraint-logic edges it controls and, for white players, a visibility area showing the edges they may see.
Locking 2-toggles shared between regions enforce the turn order, delay lines of 1-toggles fix the timing, and win gadgets
punish every deviation, so the white team has a forced win in the gadget game iff it has one in the constraint-logic game. For
an arbitrary interacting-tunnel reversible deterministic gadget, each locking 2-toggle is replaced by its simulation from the
one-player section, with special care for the gadgets shared by two players and with a visibility construction that lets a
white player observe an edge without interfering.

## Sources

- E. D. Demaine, D. H. Hendrickson, J. Lynch, "Toward a general complexity theory of motion planning: characterizing which gadgets make games hard", in *11th Innovations in Theoretical Computer Science Conference (ITCS 2020)*, Leibniz International Proceedings in Informatics 151, Schloss Dagstuhl, 2020, article 62, doi:[10.4230/LIPIcs.ITCS.2020.62](https://doi.org/10.4230/LIPIcs.ITCS.2020.62). Numbering of the version read, arXiv:1812.03592v2 (titled "Toward a General Theory of Motion Planning Complexity: Characterizing Which Gadgets Make Games Hard"): Section 4: Theorem 15 (the locking 2-toggle), Theorem 16 (arbitrary interacting-tunnel reversible deterministic gadgets), Lemma 14 (membership in RE) and the discussion of Team Private Constraint Logic before Theorem 15; Theorems 12 and 13 (the two-player case).
