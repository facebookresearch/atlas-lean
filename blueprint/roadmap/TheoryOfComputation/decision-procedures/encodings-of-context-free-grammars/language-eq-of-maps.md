# Grammars with renamings in both directions generate the same language

Let $g$ and $G$
be context-free grammars over the same terminals. Suppose there are maps $f$ from the
nonterminals of $g$ to those of $G$ and $b$ from the nonterminals of $G$ to those of $g$ such
that renaming the nonterminals of any production of $g$ by $f$ gives a production of $G$,
renaming the nonterminals of any production of $G$ by $b$ gives a production of $g$, $f$ sends
the start nonterminal of $g$ to that of $G$, and $b$ sends the start nonterminal of $G$ to that
of $g$. Then $g$ and $G$ generate the same language. The renamings need not be inverse to each
other.
