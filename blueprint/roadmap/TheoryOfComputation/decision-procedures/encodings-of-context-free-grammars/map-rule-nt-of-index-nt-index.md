# Numbering the nonterminals of a production and back recovers it

Let $G$ be a context-free
grammar over $T$ and $r$ a production of $G$. Replacing each nonterminal $A$ of $r$ by its number,
the position, counting from $0$, of the first occurrence of $A$ in the list of nonterminals that
$G$ mentions, and then replacing each number $n$ by the nonterminal of $G$ with number $n$ (the
entry at position $n$ of that list, or the initial nonterminal of $G$ if the list has no such
entry) gives $r$ again.
