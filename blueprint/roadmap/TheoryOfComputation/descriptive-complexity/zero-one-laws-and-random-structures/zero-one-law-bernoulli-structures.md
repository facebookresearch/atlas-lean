# 0-1 laws for random relational structures with constant probabilities

Let $\sigma$ be a finite relational vocabulary without nullary symbols and assign to each symbol $R$ a probability $p_R \in (0,1)$. In the random $\sigma$-structure on $\{0,\dots,n-1\}$ in which every atomic fact $R(\bar a)$ holds independently with probability $p_R$, every first-order sentence has limiting probability $0$ or $1$, and the limit does not depend on the $p_R$. The hypothesis on nullary symbols is necessary: a nullary symbol $P$ has probability $p_P$ for every $n$, so the 0-1 law fails whenever $\sigma$ has a nullary symbol.

## Proof sketch

Extension axioms for $\sigma$ hold almost surely for constant probabilities, their theory is $\aleph_0$-categorical with no finite models, and the transfer lemma applies; for a nullary symbol compute its probability directly.

## Depends on

- [Extension axioms and the theory of the random graph](extension-axioms-random-graph.md)

## Proof depends on

- [Extension axioms hold almost surely](extension-axioms-hold-almost-surely.md)
- [The theory of the random graph is $\aleph_0$-categorical and complete](random-graph-theory-categorical-and-complete.md)
- [Transfer from almost-sure theories to zero-one laws](transfer-to-zero-one-laws.md)

## Sources

- R. Fagin, "Probabilities on Finite Models", The Journal of Symbolic Logic 41(1), 50–58, 1976.
- Yu. V. Glebskiĭ, D. I. Kogan, M. I. Liogon'kiĭ and V. A. Talanov, "Range and Degree of Realizability of Formulas in the Restricted Predicate Calculus", Cybernetics 5(2), 142–154, 1969.
- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
