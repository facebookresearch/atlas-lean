# Elimination of $\varepsilon$-productions

For a context-free grammar $g$, the grammar
obtained from $g$ by eliminating $\varepsilon$-productions has the same nonterminals and the
same initial nonterminal as $g$. Its productions are the productions $A \to \alpha'$ such that
$g$ has a production $A \to \alpha$, the form $\alpha'$ is obtained from $\alpha$ by deleting
some (possibly no) occurrences of nullable nonterminals (those deriving the empty word in $g$),
and $\alpha'$ is nonempty.
