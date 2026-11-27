# Büchi–Elgot–Trakhtenbrot theorem

Let $\Sigma$ be a finite alphabet and view a nonempty word $w = a_1 \cdots a_n$ as the structure with universe $\{1, \dots, n\}$, the order $<$ and, for each $a \in \Sigma$, the unary predicate $P_a = \{i : a_i = a\}$. A language $L \subseteq \Sigma^+$ is definable by a sentence of monadic second-order logic over these structures if and only if $L$ is regular. Both directions are effective: a formula is translated into a finite automaton by induction on the formula, using projection for existential set quantifiers, and an automaton into a formula that guesses an accepting run with one set variable per state.

## Depends on

- [Monadic second-order logic over words](monadic-second-order-logic-over-words.md)

## Proof depends on

- [Homomorphic images of regular languages over finite alphabets are regular](../../regular-languages/automata-and-expressions/closure-properties-of-regular-languages/hom-image.md)

## Expansion

This page becomes ready once:

- Closure of regular languages of finite words under union, intersection and complement (proof prerequisite; not yet stated)

## Sources

- J. R. Büchi, "Weak second-order arithmetic and finite automata", *Zeitschrift für mathematische Logik und Grundlagen der Mathematik* 6:66–92, 1960
- W. Thomas, "Languages, automata, and logic", in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997
