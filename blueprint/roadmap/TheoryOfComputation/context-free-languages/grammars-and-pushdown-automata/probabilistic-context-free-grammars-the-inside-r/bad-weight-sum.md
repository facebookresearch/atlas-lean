# The constant-one weights sum to two

The ambiguous example grammar has one nonterminal $A$, which is its start symbol, one terminal $a$, and the two rules $A \to A\,A$ and $A \to a$. Under the constant-one weight function, the weights of the rules with left-hand side $A$ sum to $2$, not $1$. The identity between the inside recurrence and the sum of tree weights still applies to these weights, since it assumes no normalization.
