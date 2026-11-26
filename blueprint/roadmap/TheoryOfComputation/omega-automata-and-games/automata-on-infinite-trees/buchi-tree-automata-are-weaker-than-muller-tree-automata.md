# Büchi tree automata are weaker than Muller tree automata

The set $T_2$ of infinite binary trees over $\{a, b\}$ in which every path carries only finitely many $b$ is accepted by a deterministic
Muller tree automaton but by no Büchi tree automaton, in the sense of [tree automata on infinite trees](tree-automata-on-infinite-trees.md),
while its complement, the trees with some path carrying infinitely many $b$, is accepted by a Büchi tree automaton (Rabin). Hence
Büchi tree automata recognize strictly fewer tree languages than Muller tree automata, and their tree languages are not closed under
complementation.

## Depends on

- [Tree automata on infinite trees](tree-automata-on-infinite-trees.md)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Examples 6.2 and 6.3 with the argument for Example 6.3, credited to Rabin (1970).
