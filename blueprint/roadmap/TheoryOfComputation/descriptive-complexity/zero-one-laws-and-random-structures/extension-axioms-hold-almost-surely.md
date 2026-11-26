# Extension axioms hold almost surely

For every constant $0 < p < 1$ and every extension axiom $\mathrm{EA}_{k,s}$, $\Pr[G(n,p) \models \mathrm{EA}_{k,s}] \to 1$ as $n \to \infty$; more precisely $\Pr[G(n,p) \not\models \mathrm{EA}_{k,s}] \le n^k (1 - \min(p, 1-p)^k)^{n-k}$. The same holds for the extension axioms of a finite relational vocabulary in the random structure in which every atomic fact holds independently with probability $p_R \in (0,1)$ depending on its symbol.

## Proof sketch

Fix distinct $x_1,\dots,x_k$; each of the other $n - k$ vertices realizes the pattern independently with probability at least $q = \min(p,1-p)^k$, so all fail with probability at most $(1-q)^{n-k}$; take a union bound over the at most $n^k$ tuples.

## Depends on

- [Extension axioms and the theory of the random graph](extension-axioms-random-graph.md)

## Sources

- R. Fagin, "Probabilities on Finite Models", The Journal of Symbolic Logic 41(1), 50–58, 1976.
- N. Alon and J. H. Spencer, The Probabilistic Method, 4th ed., Wiley, 2016.
- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
