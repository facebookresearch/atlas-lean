# The pushdown modular game problem is undecidable

No algorithm decides whether player 0 has a winning modular strategy in a modular game on a recursive game graph whose winning
condition is given by a deterministic pushdown automaton.

**Theorem.** The pushdown modular game problem for [recursive game graphs](modular-games-on-recursive-game-graphs.md) is undecidable,
already when the winning condition is given by a deterministic pushdown automaton (Theorem 1 of the source). The proof reduces emptiness of the intersection of two deterministic [context-free languages](../../../context-free-languages/grammars-and-pushdown-automata/context-free-languages.md): player 1 challenges player 0 to produce a word, and player 0 has a winning modular strategy exactly when the intersection is nonempty.

The undecidability comes from the stack of the specification automaton, which is not synchronized with the call-return structure of
the game graph. For winning conditions given by visibly pushdown automata, whose stack follows the calls and returns, the modular game
problem is decidable, and [EXPTIME](../../../complexity-classes/time-and-space-complexity-classes/exp.md)-complete for deterministic or universal [Büchi](../../emptiness-of-b-chi-automata/mem-language-iff.md) and co-Büchi visibly pushdown specifications.

## Depends on

- [Modular games on recursive game graphs](modular-games-on-recursive-game-graphs.md)
- [Pushdown automaton](../../../context-free-languages/grammars-and-pushdown-automata/pushdown-automata/pda.md)
- [Visibly pushdown automata and visibly pushdown languages](../../../context-free-languages/visibly-pushdown-languages/visibly-pushdown-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the emptiness of the intersection of two deterministic context-free languages $L_1, L_2$, which is undecidable. The game
graph has a main module in which player 1 chooses between two nodes labeled $a_1$ and $a_2$, both leading to a call of a second module $m$, in
which player 0 alone generates a word. A modular strategy in $m$ cannot see which choice player 1 made, so it produces the same word
in both plays. A deterministic pushdown automaton checks the word after $a_1$ against $L_1$ and after $a_2$ against $L_2$, so player 0 has
a winning modular strategy exactly when $L_1 \cap L_2$ is nonempty.

## Sources

- I. De Crescenzo, S. La Torre and Y. Velner, "Visibly pushdown modular games", in *GandALF 2014*, Electronic Proceedings in Theoretical Computer Science 161, pp. 260–274, 2014, doi:10.4204/EPTCS.161.22; journal version *Information and Computation* 253:204–223, 2017, doi:10.1016/j.ic.2016.07.007. Read in arXiv:1408.5969v1: Theorem 1 with the reduction before it in Section 3, and Theorems 2, 3 and 4 (visibly pushdown specifications) in Section 4.
