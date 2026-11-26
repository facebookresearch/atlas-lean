# Acceptance of a tree as a game

Let $\mathcal{A}$ be a [tree automaton](tree-automata-on-infinite-trees.md) and $t$ an infinite tree. The game $\Gamma_{\mathcal{A}, t}$ is played by
*Automaton* and *Pathfinder*: from a position $(w, t(w), q)$, Automaton chooses a transition $(q, t(w), q', q'')$ of $\mathcal{A}$, and
Pathfinder chooses a direction, moving to $(w0, t(w0), q')$ or $(w1, t(w1), q'')$; the initial position is $(\varepsilon, t(\varepsilon), q_0)$.
Automaton wins an infinite play if the sequence of states it builds satisfies the acceptance condition of $\mathcal{A}$, and loses a finite
play that reaches a position where $\mathcal{A}$ has no transition; equivalently, $\mathcal{A}$ may first be completed by a rejecting sink state, after
which every play is infinite. Then
$\mathcal{A}$ accepts $t$ if and only if Automaton has a winning strategy in $\Gamma_{\mathcal{A}, t}$ from the initial position: a successful run
fixes the transitions along every path, and conversely.

## Depends on

- [Tree automata on infinite trees](tree-automata-on-infinite-trees.md)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Section 6.2, the definition of the game $\Gamma_{\mathcal{A}, t}$, and Remark 6.7.
