# Monadic second-order logic over words

Fix a finite alphabet $\Sigma$. A finite word $w = a_1 \cdots a_n$ is identified with the structure whose universe is the set of positions $\{1, \dots, n\}$, with the order $<$ and, for each $a \in \Sigma$, the unary predicate $P_a$ of positions carrying $a$. Formulas of monadic second-order logic (MSO) over $\Sigma$ use first-order variables $x, y, \dots$ for positions and second-order variables $X, Y, \dots$ for sets of positions, atomic formulas $x < y$, $P_a(x)$ and $x \in X$, Boolean connectives and quantification over both kinds of variables. A sentence $\varphi$ defines the language $L(\varphi)$ of words satisfying it. The weak and full monadic theories of $(\mathbb{N}, <)$ (WS1S and S1S) are the analogous logics over the natural numbers, with set variables ranging over finite or arbitrary sets.

## Sources

- W. Thomas, "Languages, automata, and logic", in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997, Sections 2.1 (word models) and 3.1
- J. R. Büchi, "Weak second-order arithmetic and finite automata", *Zeitschrift für mathematische Logik und Grundlagen der Mathematik* 6:66–92, 1960
