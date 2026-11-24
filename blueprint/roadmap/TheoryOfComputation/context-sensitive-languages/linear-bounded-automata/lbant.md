# Nonterminals of the grammar of a linear bounded automaton

Let $Q$ and $\Gamma$ be sets. The nonterminals of the grammar of a linear bounded automaton with state set
$Q$ and tape alphabet $\Gamma$ are of three kinds: a cell nonterminal $\langle a, x, s, f, \beta\rangle$
for each original symbol $a \in \Gamma$, current symbol $x$ (a letter of $\Gamma$ or a blank), head state
$s$ (a state of $Q$, or $\bot$ if the head is not on the cell), activity flag $f \in \{0, 1\}$ and boundary
tag $\beta$ (middle, left, right or both); the generator, which produces the remaining cells and then
disappears; and the start symbol, the initial nonterminal. Distinct data give distinct nonterminals.
