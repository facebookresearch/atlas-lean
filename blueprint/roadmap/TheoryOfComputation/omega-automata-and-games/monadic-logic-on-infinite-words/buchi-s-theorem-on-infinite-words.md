# Büchi's theorem on monadic second-order logic over infinite words

Let $\Sigma$ be a finite alphabet and view an infinite word $\alpha = a_0 a_1 \cdots \in \Sigma^\omega$ as the structure with universe
$\mathbb{N}$, the successor relation, the order $<$ and, for each $a \in \Sigma$, the unary predicate of the positions carrying $a$.
An $\omega$-language $L \subseteq \Sigma^\omega$ is recognized by a nondeterministic [Büchi automaton](../emptiness-of-b-chi-automata/mem-language-iff.md) if and only if it is
definable by a sentence of [monadic second-order logic](../logic-and-tree-automata/monadic-second-order-logic-over-words.md) over these structures, and both translations are effective
(Büchi). From an automaton, a formula guesses an accepting run with one set variable per state and requires a final state at
infinitely many positions; from a formula, an automaton is built by induction on the formula, using closure of Büchi
automata under union, complementation and projection.

## Depends on

- [Monadic second-order logic over words](../logic-and-tree-automata/monadic-second-order-logic-over-words.md)
- [Büchi acceptance condition](../emptiness-of-b-chi-automata/mem-language-iff.md)

## Proof depends on

- [MSO₀: monadic logic with set variables only](mso0-logic.md)
- [Büchi automata for the atomic MSO₀ formulas](buchi-automata-for-atomic-mso0-formulas.md)
- [Büchi automata are closed under projection](buchi-automata-are-closed-under-projection.md)
- [Languages of Büchi automata are MSO-definable](buchi-automata-are-mso-definable.md)
- [Büchi automata are closed under complementation](../boolean-closure-of-b-chi-automata/exists-buchi-compl.md)
- [Büchi automata are closed under union](../boolean-closure-of-b-chi-automata/exists-buchi-sup.md)
- [Büchi automata are closed under intersection](../boolean-closure-of-b-chi-automata/exists-buchi-inf.md)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Section 2.1 ($\omega$-word models), Theorem 5.9 and its proof, and the discussion before Section 5.2 of Büchi's original proof by complementation.
