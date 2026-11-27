# Büchi arithmetic is decidable

Statement: Büchi arithmetic is decidable. Consider the first-order language with function symbols $0$, $S$, $+$ and the binary relation symbol $V_2$, interpreted in $\mathbb{N}$ by zero, successor, addition and $V_2(x, y) \iff$ $y$ is the largest power of $2$ dividing $x$ (false for $x = 0$). Then the set

$$\{\, n \in \mathbb{N} : n = \ulcorner \varphi \urcorner \text{ for some sentence } \varphi \text{ with } \mathbb{N} \models \varphi \,\}$$

is computable, where $\ulcorner \varphi \urcorner$ is the Gödel numbering of sentences by iterated pairing with tags $0$ to $4$ for $\bot$, equality, $V_2$, implication and $\forall$. An explicit numbering is used because the mere existence of a Boolean-valued characteristic function on sentences would not express algorithmic decidability. Büchi arithmetic corresponds to the weak monadic second-order theory of one successor (WS1S) when a number is represented by the finite set of positions of the $1$s in its binary expansion, not by a single position; the approach of the sources is Büchi's automata construction.

## Sources

- J. R. Büchi, "Weak second-order arithmetic and finite automata", Zeitschrift für mathematische Logik und Grundlagen der Mathematik 6 (1960), 66-92.
- J. R. Büchi, "On a decision method in restricted second order arithmetic", Proceedings of the 1960 International Congress on Logic, Methodology and Philosophy of Science, Stanford University Press, 1962, 1-11.
