# Marker-insertion grammar

Let $g$ be a context-free grammar over $T'$ with start symbol
$A_0$, and let $T$ be a finite alphabet. The marker-insertion grammar of $g$ is the context-free
grammar over $T \sqcup T'$ whose nonterminals are those of $g$ together with a new start symbol
$S$ and a marker $D$, and whose rules are: for each rule $A \to \alpha$ of $g$, the rule
$A \to \alpha'$, where $\alpha'$ is $\alpha$ with $D$ inserted in front of each terminal; the
rule $S \to A_0 D$; the rule $D \to \varepsilon$; and the rule $D \to a D$ for each $a \in T$.
