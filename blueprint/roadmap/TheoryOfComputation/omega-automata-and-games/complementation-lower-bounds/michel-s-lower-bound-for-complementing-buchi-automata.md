# Michel's lower bound for complementing Büchi automata

For every $n \ge 1$ there is an $\omega$-language $L_n$ over the alphabet $\{1, \dots, n, \#\}$ that is recognized by a nondeterministic
[Büchi automaton](../emptiness-of-b-chi-automata/mem-language-iff.md) with $n + 2$ states, while every Büchi automaton recognizing its complement
$\{1, \dots, n, \#\}^\omega \setminus L_n$ has at least $n!$ states (Michel). A word belongs to $L_n$ exactly when, for some cycle
$(i_1 i_2)(i_2 i_3) \cdots (i_k i_1)$ of pairs of letters from $\{1, \dots, n\}$, each pair occurs infinitely often as a factor; the words
$(i_1 \cdots i_n \#)^\omega$ for the $n!$ permutations of $1, \dots, n$ lie outside $L_n$, and accepting runs of a complement automaton on
two of them must loop through disjoint sets of states. Coding the letter $i$ as $0^i 1$ gives the same bound over the fixed alphabet
$\{0, 1, \#\}$ with automata for $L_n$ whose size is linear in $n$.

## Depends on

- [Büchi acceptance condition](../emptiness-of-b-chi-automata/mem-language-iff.md)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Theorem 5.8 and its proof, credited to an unpublished example of M. Michel (1988).
