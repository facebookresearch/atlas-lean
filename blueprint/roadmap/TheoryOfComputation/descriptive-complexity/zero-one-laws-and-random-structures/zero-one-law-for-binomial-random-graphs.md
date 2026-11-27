# The 0-1 law for $G(n,p)$ with constant edge probability

Fix $0 < p < 1$. For every first-order sentence $\varphi$ in the language of graphs, $\Pr[G(n,p) \models \varphi]$ converges to $0$ or $1$, and the limit is $1$ exactly when $\varphi$ holds in the Rado graph. In particular the almost-sure first-order theory of $G(n,p)$ does not depend on the constant $p$: it is the complete decidable theory $T_{\mathrm{rg}}$ of the extension axioms, and no graph property whose probability fails to converge to $0$ or $1$ (such as having an even number of vertices) is first-order definable. For $p=1/2$ this is the 0-1 law of Glebskiĭ, Kogan, Liogon'kiĭ and Talanov and of Fagin.

## Proof sketch

The extension axioms hold almost surely in $G(n,p)$ for every constant $p$; the rest of the argument is measure-independent.

## Depends on

- [The uniform random graph $G(n, 1/2)$ and $G(n, p)$](uniform-random-graph.md)
- [Extension axioms and the theory of the random graph](extension-axioms-random-graph.md)
- [The Rado graph is the countable random graph](rado-graph-countable-random-graph.md)

## Proof depends on

- [Extension axioms hold almost surely](extension-axioms-hold-almost-surely.md)
- [Transfer from almost-sure theories to zero-one laws](transfer-to-zero-one-laws.md)
- [The theory of the random graph is $\aleph_0$-categorical and complete](random-graph-theory-categorical-and-complete.md)

## Sources

- Yu. V. Glebskiĭ, D. I. Kogan, M. I. Liogon'kiĭ and V. A. Talanov, "Range and Degree of Realizability of Formulas in the Restricted Predicate Calculus", Cybernetics 5(2), 142–154, 1969.
- N. Alon and J. H. Spencer, The Probabilistic Method, 4th ed., Wiley, 2016.
- R. Fagin, "Probabilities on Finite Models", The Journal of Symbolic Logic 41(1), 50–58, 1976.
