# Derivations transfer along a renaming of nonterminals

Let $g$ and $G$ be context-free
grammars over the same terminal alphabet, and let $f$ map the nonterminals of $g$ to those of $G$.
Extend $f$ to symbols and sentential forms by renaming each nonterminal and keeping each terminal.
Suppose that for every production $A \to \alpha$ of $g$, the renamed production $f(A) \to f(\alpha)$
is a production of $G$. Then whenever a sentential form $u$ derives $v$ in $g$ (in zero or more
steps), $f(u)$ derives $f(v)$ in $G$.

No injectivity of $f$ is needed for this direction.
