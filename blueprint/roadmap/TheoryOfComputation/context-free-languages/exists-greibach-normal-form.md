# Greibach normal form: every context-free grammar has an equivalent one

A context-free grammar with start symbol $S$ is in Greibach normal form when

- every production is either $S \to \varepsilon$ or of the form $A \to a B_1 \cdots B_m$ with a terminal $a$ and nonterminals $B_1, \dots, B_m$ ($m \ge 0$), and
- either $S$ occurs on the right-hand side of no production, or no production has the empty right-hand side.

The following holds: for every context-free grammar $g$ over a terminal alphabet $T$ there is a context-free grammar $g'$ over $T$ in Greibach normal form with $L(g') = L(g)$.

For a language containing the empty word, apply the theorem to the language without it and add a fresh start symbol $S'$ with a copy of each production of the old start symbol and the production $S' \to \varepsilon$; $S'$ occurs on no right-hand side.

## Sources

- J. E. Hopcroft and J. D. Ullman, *Introduction to Automata Theory, Languages, and Computation*, Addison-Wesley, 1979, §4.6, Theorem 4.6, for languages without the empty word.
- M. A. Harrison, *Introduction to Formal Language Theory*, Addison-Wesley, 1978, Chapter 4.
