# Cutoff sums are the total weights of bounded example trees

The ambiguous example grammar has one nonterminal $A$, which is its start symbol, one terminal $a$, and the two rules $A \to A\,A$ and $A \to a$. The depth of a leaf is $1$, and the depth of a node is one more than the larger depth of its subtrees. Let real rule weights give $p$ to $A \to A\,A$ and $q$ to $A \to a$, and define $S_0 = S_1 = 0$ and $S_{h+1} = q + p\,S_h^2$ for $h \ge 1$. For every $h$, the valid derivation trees of the grammar of depth at most $h$ have total weight $S_{h+1}$.
