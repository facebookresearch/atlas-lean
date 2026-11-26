# The Chi and Geman weights on the example grammar

The ambiguous example grammar has one nonterminal $A$, which is its start symbol, one terminal $a$, and the two rules $A \to A\,A$ and $A \to a$. The Chi and Geman weight function gives weight $1/3$ to every rule whose right-hand side is a single terminal, so to $A \to a$, and weight $2/3$ to every other rule, so to $A \to A\,A$. These weights are normalized.
