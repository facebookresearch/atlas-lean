# Turning a binary tree into an example derivation tree preserves depth

The ambiguous example grammar has one nonterminal $A$, which is its start symbol, one terminal $a$, and the two rules $A \to A\,A$ and $A \to a$. Every one-nonterminal binary tree becomes a derivation tree of this grammar of the same shape, with leaves $A \to a$ and nodes $A \to A\,A$. Depths of both kinds of tree are $1$ for a leaf and one more than the larger subtree depth for a node. For every binary tree, the depth of the corresponding derivation tree equals its own depth.
