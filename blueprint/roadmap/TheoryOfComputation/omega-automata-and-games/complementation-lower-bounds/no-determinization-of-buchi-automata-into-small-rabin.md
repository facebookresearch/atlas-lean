# No determinization of Büchi automata into small Rabin automata

There is no construction that converts every nondeterministic [Büchi automaton](../emptiness-of-b-chi-automata/mem-language-iff.md) with $n$ states into an equivalent deterministic
[Rabin automaton](../rabin-and-streett-automata/rabin.md) with $2^{O(n)}$ states and $O(n)$ accepting pairs. Such a construction,
applied to the automata of Michel's languages $L_n$ and followed by complementing the deterministic Rabin automaton into a
nondeterministic Büchi automaton with $2^{O(n)}$ states, which guesses from which point on the Streett condition dual to the Rabin
pairs is checked, would contradict the $n!$ lower bound. Safra's determinization, with $2^{O(n \log n)}$ states, is therefore optimal in
this sense.

## Depends on

- [Büchi acceptance condition](../emptiness-of-b-chi-automata/mem-language-iff.md)
- [Rabin automaton](../rabin-and-streett-automata/rabin.md)

## Proof depends on

- [Michel's lower bound for complementing Büchi automata](michel-s-lower-bound-for-complementing-buchi-automata.md)
- [Run-wise Rabin/Streett duality](../rabin-and-streett-automata/accepts-run-iff-not-streett.md)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Theorem 5.7 and its proof, and the bound on the number of Safra trees before it.
