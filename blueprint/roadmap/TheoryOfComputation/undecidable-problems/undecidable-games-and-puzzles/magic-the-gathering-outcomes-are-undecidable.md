# Determining the outcome of a game of Magic: The Gathering is undecidable

No algorithm decides, from a given state of a two-player game of Magic: The Gathering in which all remaining moves of both players are forced, which player will win; a universal Turing machine can be embedded in such a game.

**Setting.** A game of Magic: The Gathering is played under the game's comprehensive rules, with standard-size tournament-legal decks, no hidden information that matters and no randomness. Any number a player chooses must be written in standard binary notation (without this convention, naming numbers by arbitrary well-defined functions would already make the next game state noncomputable). A game in which all remaining moves are forced is one in which, from the given state on, no player has a nontrivial decision left; a deterministic infinite loop is a draw by the rules.

**Theorem (Churchill, Biderman and Herrick).** Determining the outcome of a game of Magic: The Gathering in which all remaining moves are forced is undecidable (Theorem 1). More precisely, for every Turing machine there is a game state, built with tournament-legal cards, in which a designated player wins if and only if the machine halts, and otherwise the game enters a deterministic infinite loop.

As deciding whether a winning move exists is no harder than playing optimally, optimal play in Magic: The Gathering is at least as hard as the halting problem. This answered the question, posed by Demaine and Hearn and by Auger and Teytaud, whether some real-world game, played under its usual rules, has undecidable perfect play; the source conjectures that optimal play is at least as hard as $\emptyset^{(\omega)}$.

## Depends on

- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The construction embeds Rogozhin's universal Turing machine with $2$ states and $18$ symbols, played out between two players Alice and Bob. The tape is a set of creature tokens whose power and toughness give their distance from the head (a $2/2$ token under the head, larger tokens further away), green tokens to the left of the head and white ones to the right, with $18$ creature types standing for the $18$ symbols. The controller is a collection of copies of cards such as Rotlung Reanimator and Xathrid Necromancer, whose triggered abilities ("whenever a creature of a given type dies, create a token") act as the conditional instructions of the machine once their creature types and colors are rewritten by Artificial Evolution and Glamerdye; reading a cell is done by Infest, which kills the unique token of toughness $2$, whose type triggers one controller card to create the token for the new symbol, and the head moves by putting $+1/+1$ counters on the tokens on one side and $-1/-1$ counters on those on the other; phasing switches between the two states. Every trigger and choice is forced. If the machine halts, Alice wins; otherwise the game is an unbreakable deterministic loop, a draw. Since the universal machine simulates every Turing machine, the halting problem reduces to the outcome of such games. A good expansion links a page for Rogozhin's small universal Turing machine.

## Sources

- Alex Churchill, Stella Biderman and Austin Herrick, "Magic: The Gathering is Turing complete", in *10th International Conference on Fun with Algorithms (FUN 2021)*, Leibniz International Proceedings in Informatics 157, paper 9, pp. 9:1–9:19, 2020, doi:[10.4230/LIPIcs.FUN.2021.9](https://doi.org/10.4230/LIPIcs.FUN.2021.9); read in the open-access published version ([PDF](https://drops.dagstuhl.de/storage/00lipics/lipics-vol157-fun2021/LIPIcs.FUN.2021.9/LIPIcs.FUN.2021.9.pdf)): Theorem 1 in Section 1, the binary-notation convention of Section 2, the construction of Sections 3 and 4, and the discussion, Open Problem 3 and Conjecture 4 of Section 5; the preprint is arXiv:1904.09828v2.
