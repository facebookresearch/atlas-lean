# Reachability by unit productions

Let $g$ be a context-free grammar. A nonterminal
$A$ of $g$ reaches a nonterminal $B$ by unit productions when there is a chain
$A = A_0, A_1, \dots, A_n = B$ with $n \ge 0$ such that each $A_{i-1} \to A_i$ is a
production of $g$. In particular, every nonterminal reaches itself.
