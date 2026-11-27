# Unit elimination for encoded grammars

For an encoded context-free grammar $g$, the
encoded grammar with the start nonterminal of $g$ whose productions are listed as follows: for
each nonterminal $A$ in the list of nonterminals of $g$, and for each production $B \to u$ of $g$
in order such that $B$ is in the computed list of nonterminals reachable from $A$ by unit
productions and $u$ is not a single nonterminal, the production $A \to u$.
