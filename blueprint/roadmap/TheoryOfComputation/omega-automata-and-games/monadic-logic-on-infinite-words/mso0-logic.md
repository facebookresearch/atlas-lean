# MSO₀: monadic logic with set variables only

Over words on an alphabet $A$, finite or infinite, *MSO₀-logic* has only set variables $X, Y, \dots$ and the atomic formulas
$X \subseteq Y$, $\mathrm{Sing}(X)$, $\mathrm{Suc}(X, Y)$ and $X \subseteq Q_a$ for $a \in A$, meaning that $X$ is a subset of $Y$, that $X$ is a singleton, that $X$ and
$Y$ are singletons $\{x\}$ and $\{y\}$ with $y$ the successor of $x$, and that every position of $X$ carries the letter $a$; formulas are closed
under Boolean connectives and set quantifiers. A formula $\varphi(X_1, \dots, X_n)$ defines the set of words over $A \times \{0,1\}^n$ whose
$k$-th extra component is the characteristic sequence of a set satisfying $\varphi$ for $X_k$. Every formula of
[monadic second-order logic](../logic-and-tree-automata/monadic-second-order-logic-over-words.md) over words is equivalent to an MSO₀-formula, effectively, by representing
each element $x$ by the singleton $\{x\}$ (so $X(x)$ becomes $\{x\} \subseteq X$).

## Depends on

- [Monadic second-order logic over words](../logic-and-tree-automata/monadic-second-order-logic-over-words.md)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Section 2.3 ("Monadic Second-Order Logic"), the paragraphs introducing MSO₀-logic, its atomic formulas and the translation from MSO-logic, and the identification of set expansions of word models with words over extended alphabets.
