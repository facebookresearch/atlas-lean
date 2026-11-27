# Büchi automata are closed under projection

Let $\pi : A \times \{0,1\}^n \to A \times \{0,1\}^{n-1}$ delete the last component, extended letterwise to infinite words. If a language
$L \subseteq (A \times \{0,1\}^n)^\omega$ is recognized by a nondeterministic [Büchi automaton](../emptiness-of-b-chi-automata/mem-language-iff.md) $\mathcal{A}$, then $\pi(L)$ is
recognized by a nondeterministic Büchi automaton with the same states: on a letter $b$ it guesses a letter $c$ with $\pi(c) = b$ and
moves as $\mathcal{A}$ does on $c$. More generally the languages of Büchi automata are closed under images by letter-to-letter maps between
alphabets. In logical terms this handles existential set quantification, $\exists X_n\, \psi(X_1, \dots, X_n)$.

## Depends on

- [Büchi acceptance condition](../emptiness-of-b-chi-automata/mem-language-iff.md)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): proof of Theorem 3.1 (closure under projection: the automaton "just has to guess (by nondeterminism)" the $n$-th component), carried over to infinite words in the proof of Theorem 5.9.
