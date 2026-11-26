# Validity of first-order sentences is undecidable

Fix an effective Gödel numbering $\sigma \mapsto \ulcorner \sigma \urcorner$ of the sentences of the language of arithmetic. The set of Gödel numbers of the sentences that hold in every structure for that language is not computable: no Turing machine, started on a natural number, halts with output $1$ exactly when the number codes a valid sentence and with output $0$ otherwise. The proof reduces the halting problem: from a machine $M$ and an input $w$ one computes a sentence that is valid exactly when $M$ halts on $w$.

## Sources

- The Open Logic Project, *Sets, Logic, Computation*, Section 15.8, Theorem 15.16 (by reduction of the halting problem), <https://builds.openlogicproject.org/courses/sets-logic-computation/slc-screen.pdf>
- A. Church, "A note on the Entscheidungsproblem", *Journal of Symbolic Logic* 1(1):40–41, 1936
- A. M. Turing, "On computable numbers, with an application to the Entscheidungsproblem", *Proceedings of the London Mathematical Society* 42:230–265, 1937
