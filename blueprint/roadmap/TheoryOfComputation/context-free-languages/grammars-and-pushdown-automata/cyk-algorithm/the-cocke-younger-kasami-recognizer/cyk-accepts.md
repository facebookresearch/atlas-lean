# The CYK recognizer

Let $g$ be a context-free grammar with initial nonterminal $S$. The
CYK recognizer accepts the empty word exactly when $g$ has a production $S \to \varepsilon$, and
accepts a nonempty word $w$ exactly when $S$ lies in the cell recorded for $w$ in the CYK table of
$w$ up to length $|w|$.
