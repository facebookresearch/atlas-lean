# Acceptable productions

Given a list $G$ of nonterminals (natural numbers), the test
accepts an encoded production $(A, \rho)$ when every symbol of $\rho$ is acceptable: a
terminal always is, and a nonterminal is when it belongs to $G$. So the production is accepted
exactly when every nonterminal occurring in $\rho$ belongs to $G$.
