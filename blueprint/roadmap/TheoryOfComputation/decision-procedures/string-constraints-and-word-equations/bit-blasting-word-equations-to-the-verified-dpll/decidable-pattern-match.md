# Decidability of Boolean-word pattern matching

Let $n \in \mathbb{N}$, let $u$ be a finite word over $\{0, 1\} \cup \{x_0, \dots, x_{n-1}\}$ (a pattern)
and let $t$ be a binary word (the target). The question whether some substitution $\sigma$ of binary words
for the variables turns $u$ into $t$ is decided by the pattern-matching procedure, which runs the bounded
word-equation solver with bound $|t|$ on the single equation $u = t$: the answer is yes exactly when the
procedure returns true.
