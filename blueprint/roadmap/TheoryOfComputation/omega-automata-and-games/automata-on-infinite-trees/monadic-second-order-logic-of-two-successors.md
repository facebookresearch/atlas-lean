# Monadic second-order logic of two successors

The *binary tree* is the structure $T = (\{0, 1\}^*, S_0, S_1)$ in which $S_i(u, v)$ holds when $v = ui$. Monadic second-order formulas over
the signature $\{S_0, S_1\}$ have first-order variables for nodes, set variables for arbitrary sets of nodes, atomic formulas
$S_0(x, y)$, $S_1(x, y)$, $x = y$ and $x \in X$, Boolean connectives and quantifiers over both kinds of variables. The theory *S2S* is the
set of such sentences true in $T$. A formula $\varphi(X_1, \dots, X_n)$ with free set variables is interpreted in the expansions
$(T, P_1, \dots, P_n)$, identified with the infinite trees over $\{0, 1\}^n$ whose label at $w$ records which of the sets $P_i$ contain $w$.

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Sections 2.1 and 2.3 and the beginning of Section 6.3.
