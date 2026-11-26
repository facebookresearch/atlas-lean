# Büchi automata for the atomic MSO₀ formulas

For each atomic [MSO₀-formula](mso0-logic.md) $X_j \subseteq X_k$, $\mathrm{Sing}(X_j)$, $\mathrm{Suc}(X_j, X_k)$ and $X_j \subseteq Q_a$ over the alphabet $A \times \{0,1\}^n$, there is a
deterministic [Büchi automaton](../emptiness-of-b-chi-automata/mem-language-iff.md) accepting exactly the infinite words that satisfy it. For example, for
$X_j \subseteq X_k$ the automaton checks at every position that a $1$ in the $j$-th extra component comes with a $1$ in the $k$-th; for
$\mathrm{Sing}(X_j)$ it checks that the $j$-th component contains exactly one $1$.

## Depends on

- [MSO₀: monadic logic with set variables only](mso0-logic.md)
- [Büchi acceptance condition](../emptiness-of-b-chi-automata/mem-language-iff.md)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): proof of Theorem 3.1 (the automata for the atomic formulas, "e.g. the finite automaton checking whether $X_j \subseteq X_k$ holds"), carried over to infinite words in the proof of Theorem 5.9.
