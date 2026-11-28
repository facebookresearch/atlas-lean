# Context-free games with nested word transducer replacement are undecidable

In left-to-right rewriting games on nested words with replacements given by nested word transducers, deciding whether the first player wins is undecidable for $\varepsilon$-free transducers with unbounded replay, and not even recursively enumerable for general transducers once call depth $2$ is allowed.

**Nested words.** For a finite alphabet $\Sigma$, a nested word is a well-nested string over opening tags $\langle a$ and closing tags $a\rangle$ ($a \in \Sigma$); it is *rooted* if it encodes a tree.

**Context-free games.** A *context-free game on nested words* $G = (\Sigma, \Gamma, R, T)$ has an alphabet $\Sigma$, a set $\Gamma \subseteq \Sigma$ of function symbols, a replacement relation $R$ between rooted nested words and nested words, and a nonempty regular target language $T$ of nested words, given by a deterministic nested word automaton. A play on a nested word $w$ moves a focus from left to right: at each closing tag $a\rangle$ the first player plays *Read* (the focus moves on) or, if $a \in \Gamma$, *Call*; after a Call the second player replaces the rooted word $u$ ending at that tag by some $v$ with $(u, v) \in R$ (if there is none, the second player wins the play at once), and the focus moves to the first symbol of $v$. The first player wins a play if it ends and the final word is in $T$; a play that never ends is not won by her. The *Call depth* of a play is the maximal nesting depth of Call moves ($0$ if no Call is played, $1$ if no Call is played inside a replacement string); a strategy has *Call depth at most $k$* if all its plays do, strategies of Call depth $1$ are *replay-free*, and *unbounded replay* means that no bound on the Call depth is imposed. $\mathsf{JWin}$ is the problem of deciding, given $G$ (its transducer and its target automaton) and a nested word $w$, whether the first player has a winning strategy on $w$, for a class of games that may restrict the Call depth of her strategies.

**Nested word transducers.** The replacement relations are given by nested word transducers: nested word automata whose opening and closing transitions also output words, subject to the source's restrictions on $\varepsilon$-transitions (only through designated hierarchical $\varepsilon$-states), well-formedness and synchronization of outputs. A transducer is *$\varepsilon$-free* if it has no $\varepsilon$-transitions and no hierarchical $\varepsilon$-states; its outputs then have length linear in its inputs.

**Theorem (Schuster).**

1. For games with $\varepsilon$-free nested word transducers and unbounded replay, $\mathsf{JWin}$ is undecidable (Theorem 18 of the source).
2. For games with nested word transducers and Call depth at most $k$, for any fixed $k \ge 2$, $\mathsf{JWin}$ is not recursively enumerable (Theorem 14).

With $\varepsilon$-free transducers and Call depth bounded by $d \ge 2$, the problem is decidable but not in elementary time, and replay-free games are $\mathrm{coNEXPTIME}$-complete ($\varepsilon$-free) or $2\mathrm{EXPTIME}$-complete (general transducers), as the same paper shows.

## Depends on

- [Nested words and nested word automata](../../../context-free-languages/visibly-pushdown-languages/nested-words-and-nested-word-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [Halting is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)
- [The halting problem is not co-recognizable by multi-stack machines](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-co-recognizable-halting.md)

## Expansion

For item 1, configurations of a Turing machine are encoded as nested words below a root $r$, and each Call on the closing tag of $r$ is answered by a functional $\varepsilon$-free transducer that replaces the configuration by its successor; the target language consists of the encodings of halting configurations, so the first player wins exactly when the machine halts on the empty input. The source shows that this remains undecidable with at most one Call per replacement string. Item 2 reduces the complement of the halting problem on the empty input: on the input $\langle s\, s\rangle$ the first player calls $s$, the second player answers with $\langle t^r v_0\, t\rangle^r$ for a number $r$ of his choice and the encoding $v_0$ of the initial configuration, intended to be the number of steps after which the machine halts; a transducer advances an encoded configuration by one step inside each $t$-tag, and the game is built so that the first player has a winning strategy exactly when the machine does not halt on the empty input.

## Sources

- M. Schuster, "Transducer-Based Rewriting Games for Active XML", in *41st International Symposium on Mathematical Foundations of Computer Science (MFCS 2016)*, Leibniz International Proceedings in Informatics (LIPIcs) 58, 2016, paper 83, doi:10.4230/LIPIcs.MFCS.2016.83; read as arXiv:1606.02879v1, <https://arxiv.org/abs/1606.02879v1>: Theorem 18 of the section on games with $\varepsilon$-free transducer replacement (item 1) and its proof in the appendix, Theorem 14, opening the section on games with general transducer replacement (item 2), the definitions of nested words, context-free games, strategies, Call depth, replay and $\mathsf{JWin}$ in the preliminaries, and the definition and restrictions of nested word transducers in the section on nested word transducers, all in that version.
