# Context-sensitive grammar

An unrestricted grammar $G$ with terminal set $T$ and nonterminal set $N$ is context-sensitive if every
production $\ell \to r$ of $G$ satisfies two conditions: $\ell$ contains at least one nonterminal (in
particular $\ell$ is nonempty), and $|\ell| \le |r|$.

There is no exception allowing a production $S \to \varepsilon$, so the language of such a grammar never
contains the empty word.
