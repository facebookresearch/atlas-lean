# The constant-one weights are not normalized

The ambiguous example grammar has one nonterminal $A$, which is its start symbol, one terminal $a$, and the two rules $A \to A\,A$ and $A \to a$. Rule weights are normalized when they are nonnegative on the rules and, for every nonterminal, the weights of the rules with that left-hand side sum to $1$. The constant-one weights are not normalized: the two rules for $A$ have total weight $2$.
