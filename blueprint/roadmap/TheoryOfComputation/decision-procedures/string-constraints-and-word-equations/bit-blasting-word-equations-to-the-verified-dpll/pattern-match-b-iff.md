# Target length bounds the pattern-matching search

Let $n \in \mathbb{N}$, let $u$ be a finite word over $\{0, 1\} \cup \{x_0, \dots, x_{n-1}\}$ and let $t$
be a binary word. The pattern-matching procedure (the bounded word-equation solver with bound $|t|$ on the
single equation $u = t$) returns true if and only if some substitution $\sigma$ of binary words for the
variables turns $u$ into $t$. No bound on $\sigma$ is assumed: the length of $t$ is a sufficient search
bound.
