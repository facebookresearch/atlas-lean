# Solvability of Baba Is You levels with an unbounded hallway is undecidable

Deciding whether a level of the block-pushing puzzle game Baba Is You can be won becomes undecidable once a two-tile-tall hallway of unbounded length is attached to one side of the level; for ordinary finite levels the question is decidable.

**Setting.** In Baba Is You the rules of a level are sentences formed by text blocks lying in the level, such as "baba is you" or "flag is win", and pushing text blocks changes the rules. Under the game's usual restrictions (at most six copies of an object on one tile and finitely many kinds of objects) a level has boundedly many reachable states, so whether it can be won is decidable. An instance of the problem *baba+2* is a finite rectangular level with a hallway two tiles tall and unbounded to the right attached to its right side, whose top and bottom behave like the level border and into which objects may move arbitrarily far; it is a yes instance if some finite sequence of moves guarantees that the player reaches the win condition at some point, ignoring the game's "Too Complex" and "Infinite Loop" screens in any state whose rules have a valid interpretation, and without ever forming a rule of the form "empty is …".

**Theorem (Geller).** The problem baba+2 is undecidable. The proof gives a polynomial-time reduction from the [Post correspondence problem with five pairs](../post-correspondence-problem/the-post-correspondence-problem-is-undecidable-f.md), encoded over a binary alphabet.

The source notes that other small modifications should suffice as well, for instance removing the cap on the number of copies of an object on one tile.

## Depends on

- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable for five pairs of words](../post-correspondence-problem/the-post-correspondence-problem-is-undecidable-f.md)

## Expansion

A good expansion adds and links definition pages for the model the statement quantifies over, as Sections 1 and 2.1 of the source fix it: baba+2 levels (the finite level, the two-tile hallway and the cap on copies of an object per tile), the rule sentences formed by text blocks, the moves and their effect on objects and rules, and the win condition.

An instance of the Post correspondence problem with five pairs over any finite alphabet becomes one over $\{0,1\}$ by replacing each letter with a binary block of fixed length, so the binary problem with five pairs is undecidable. From such an instance $(\alpha_i,\beta_i)_{i\le5}$ the level contains five button gadgets, one for each pair, together with a timer gadget and a duplication gadget per pair, whose arrangement of lava and ice objects is read off the two words of the pair. Until the player pushes a wall text down, the only possible interactions are pushing the text "is" up in the button gadgets, in some order, and each push replicates the lava and ice tiles of the corresponding pair in two rows at the bottom of the level, which extend into the hallway; the top words, read in the reverse order of the pushes, appear in one row with lava for $1$, and the bottom words in the other row with lava for $0$. The only winning rule is "level without lava and without ice is win", and pushing the wall down removes the tiles exactly when the two rows are complementary in every column, that is, when the chosen sequence of indices solves the instance. The level has size polynomial in the instance.

## Sources

- Jonathan Geller, "Baba is You is undecidable", in *2023 IEEE Conference on Games (CoG)*, pp. 1–8, IEEE, 2023, doi:[10.1109/CoG57401.2023.10333219](https://doi.org/10.1109/CoG57401.2023.10333219); read in arXiv:2205.00127v1 ([arXiv](https://arxiv.org/abs/2205.00127v1)): the definitions of baba+2 in Section 1 and of the five-pair binary Post correspondence problem in Section 2.2, the decidability of unmodified levels in Section 2.1, the reduction of Section 3 with the concluding equivalence, and Section 4.
