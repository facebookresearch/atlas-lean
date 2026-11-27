# The example derivation tree with a given shape

The ambiguous example grammar has one nonterminal $A$, which is its start symbol, one terminal $a$, and the two rules $A \to A\,A$ and $A \to a$. A one-nonterminal binary tree is turned into a derivation tree of this grammar recursively: a leaf becomes the leaf for $A \to a$, and a node with subtrees $l$ and $r$ becomes the node for $A \to A\,A$ whose subtrees are the derivation trees for $l$ and $r$.
