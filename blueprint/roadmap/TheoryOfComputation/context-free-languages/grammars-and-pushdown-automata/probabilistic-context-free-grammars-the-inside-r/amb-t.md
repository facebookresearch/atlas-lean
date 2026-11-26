# The right-associated parse of aaa

The ambiguous example grammar has one nonterminal $A$, which is its start symbol, one terminal $a$, and the two rules $A \to A\,A$ and $A \to a$. Its right-associated derivation tree for $a\,a\,a$ is the node for $A \to A\,A$ whose left subtree is a leaf $A \to a$ and whose right subtree is the node for $A \to A\,A$ with two leaves $A \to a$; it groups the word as $a\,(a\,a)$.
