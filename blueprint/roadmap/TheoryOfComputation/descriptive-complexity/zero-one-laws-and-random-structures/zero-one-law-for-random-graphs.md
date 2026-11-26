# Glebskiĭ et al. and Fagin: the 0-1 law for random graphs

For every first-order sentence $\varphi$ in the language of graphs, $\Pr[G(n,1/2) \models \varphi]$ converges to $0$ or to $1$ as $n \to \infty$. The limit is $1$ if and only if $\varphi$ holds in the Rado graph, equivalently iff $T_{\mathrm{rg}} \models \varphi$. Consequently the almost-sure theory of $G(n,1/2)$ is the complete decidable theory $T_{\mathrm{rg}}$, and no graph property whose probability fails to converge to $0$ or $1$ (such as having an even number of edges or vertices) is first-order definable.

## Proof sketch

This is the case $p = 1/2$ of the 0-1 law for $G(n,p)$: extension axioms hold almost surely, and their theory is complete; apply the transfer lemma. Rado's graph is the countable model, so truth in it decides the limit.

## Depends on

- [The uniform random graph $G(n, 1/2)$ and $G(n, p)$](uniform-random-graph.md)
- [Extension axioms and the theory of the random graph](extension-axioms-random-graph.md)

## Proof depends on

- [The 0-1 law for $G(n,p)$ with constant edge probability](zero-one-law-for-binomial-random-graphs.md)
- [Extension axioms hold almost surely](extension-axioms-hold-almost-surely.md)
- [The theory of the random graph is $\aleph_0$-categorical and complete](random-graph-theory-categorical-and-complete.md)
- [Transfer from almost-sure theories to zero-one laws](transfer-to-zero-one-laws.md)
- [The Rado graph is the countable random graph](rado-graph-countable-random-graph.md)

## Sources

- Yu. V. Glebskiĭ, D. I. Kogan, M. I. Liogon'kiĭ and V. A. Talanov, "Range and Degree of Realizability of Formulas in the Restricted Predicate Calculus", Cybernetics 5(2), 142–154, 1969.
- R. Fagin, "Probabilities on Finite Models", The Journal of Symbolic Logic 41(1), 50–58, 1976.
- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
