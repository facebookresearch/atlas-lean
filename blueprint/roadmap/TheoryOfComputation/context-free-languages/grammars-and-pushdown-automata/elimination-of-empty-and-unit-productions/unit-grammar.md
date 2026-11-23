# Eliminating unit productions

A unit production is one whose output is a single
nonterminal. For a context-free grammar $g$, the grammar obtained by eliminating unit
productions has the same nonterminals and the same start symbol as $g$. Its productions
are the $A \to \alpha$ such that $A$ is a nonterminal mentioned by $g$ (its start symbol
or one occurring in a production of $g$), $g$ has a production $B \to \alpha$ that is not
a unit production, and $A$ reaches $B$ by a chain of zero or more unit productions of $g$.
