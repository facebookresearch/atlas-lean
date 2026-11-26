# Nonterminals in outputs have no empty production

Let $g$ be a context-free grammar in
Chomsky normal form. If a nonterminal $B$ occurs in the output of some production of $g$, then
$g$ has no production $B \to \varepsilon$.

Such a production would have the initial nonterminal on the left, which then occurs in an output
while an empty production exists.
