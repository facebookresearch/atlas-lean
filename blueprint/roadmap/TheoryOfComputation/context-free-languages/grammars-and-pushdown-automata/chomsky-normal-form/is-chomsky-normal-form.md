# Chomsky normal form

Let $T$ be an alphabet. A context-free grammar $G$ with terminals $T$ and initial nonterminal $S$ is in
Chomsky normal form if every production has one of the forms $A \to BC$ (two nonterminals $B, C$), $A \to a$
(a single terminal $a$), or $S \to \varepsilon$ (empty right side, with left side the initial nonterminal),
and moreover either $S$ occurs on the right side of no production or no production has empty right side.

The second condition prevents an empty production for $S$ from making the empty word derivable from other
nonterminals.
