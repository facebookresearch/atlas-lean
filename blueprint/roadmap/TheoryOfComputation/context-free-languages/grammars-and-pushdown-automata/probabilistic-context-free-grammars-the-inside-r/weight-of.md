# Weight of a derivation tree

For weights $q$ on context-free rules, the weight of a binary derivation tree is the product of the weights of the rules it uses: a leaf for the rule $A \to a$ has weight $q(A \to a)$, and a node for the rule $A \to B\,C$ with subtrees $l$ and $r$ has weight $q(A \to B\,C)\, w(l)\, w(r)$.
